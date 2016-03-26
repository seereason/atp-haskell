-- | Model elimination procedure (MESON version, based on Stickel's PTTP).
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Logic.ATP.Meson
    ( meson1
    , meson2
    , meson
    , testMeson
    ) where

import Control.Monad.State (execStateT)
import Data.Logic.ATP.Apply (HasApply(TermOf, PredOf), pApp)
import Data.Logic.ATP.FOL (generalize, IsFirstOrder)
import Data.Logic.ATP.Formulas (false, IsFormula(AtomOf))
import Data.Logic.ATP.Lib (Depth(Depth), deepen, Failing(Failure, Success), setAll, settryfind)
import Data.Logic.ATP.Lit ((.~.), JustLiteral, LFormula, negative)
import Data.Logic.ATP.Parser (fof)
import Data.Logic.ATP.Pretty (assertEqual', prettyShow, testEquals)
import Data.Logic.ATP.Prolog (PrologRule(Prolog), renamerule)
import Data.Logic.ATP.Prop ((.&.), (.|.), (.=>.), list_conj, PFormula, simpcnf)
import Data.Logic.ATP.Quantified (exists, for_all, IsQuantified(VarOf))
import Data.Logic.ATP.Resolution (davis_putnam_example_formula)
import Data.Logic.ATP.Skolem (askolemize, Formula, HasSkolem(SVarOf), pnf, runSkolem, SkolemT, simpdnf', specialize, toSkolem)
import Data.Logic.ATP.Tableaux (K(K), tab)
import Data.Logic.ATP.Term (fApp, IsTerm(FunOf, TVarOf), vt)
import Data.Logic.ATP.Unif (Unify(UTermOf), unify_literals)
import Data.Map.Strict as Map
import Data.Set as Set
import Test.HUnit

test03 :: Test
test03 = let fm = [fof| ∀a. ¬(P(a)∧(∀y. (∀z. Q(y)∨R(z))∧¬P(a))) |] in
         $(testEquals "TAB 1") (Success ((K 2, Map.empty),Depth 2)) (tab Nothing fm)

test04 :: Test
test04 = let fm = [fof| ∀a. ¬(P(a)∧¬P(a)∧(∀y z. Q(y)∨R(z))) |] in
         $(testEquals "TAB 2") (Success ((K 0, Map.empty),Depth 0)) (tab Nothing fm)

        {- fm3 = [fof| ¬p ∧ (p ∨ q) ∧ (r ∨ s) ∧ (¬q ∨ t ∨ u) ∧
                    (¬r ∨ ¬t) ∧ (¬r ∨ ¬u) ∧ (¬q ∨ v ∨ w) ∧
               (¬s ∨ ¬v) ∧ (¬s ∨ ¬w) |] -}

{-
START_INTERACTIVE;;
tab <<forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))>>;;

tab <<forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The interesting example where tableaux connections make the proof longer. *)
(* Unfortuntely this gets hammered by normalization first...                 *)
(* ------------------------------------------------------------------------- *)

tab <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
      (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
      (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
END_INTERACTIVE;;
-}
-- -------------------------------------------------------------------------
-- Example of naivety of tableau prover.
-- -------------------------------------------------------------------------

test05 :: Test
test05 = $(testEquals "test001") (Success ((K 0, Map.empty), Depth 0))
         (tab Nothing [fof| ¬p∧(p∨q)∧(r∨s)∧(¬q∨t∨u)∧(¬r∨¬t)∧(¬r∨¬u)∧(¬q∨v∨w)∧(¬s∨¬v)∧(¬s∨¬w)⇒⊥|])

test01 :: Test
test01 = TestLabel "Meson 1" $ TestCase $ assertEqual' "meson dp example (p. 220)" expected input
    where input = runSkolem (meson (Just (Depth 10)) (davis_putnam_example_formula :: Formula))
          expected :: Set (Failing Depth)
          expected = Set.singleton (Success (Depth 8))

test06 :: Test
test06 = $(testEquals "meson dp example, step 1 (p. 220)") [fof| ∃x y. (∀z. (F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z))) |]
           davis_putnam_example_formula

test02 :: Test
test02 =
    TestLabel "Meson 2" $
    TestList [TestCase (assertEqual' "meson dp example, step 2 (p. 220)"
                                    (exists "x" (exists "y" (for_all "z" (((f [x,y]) .=>. ((f [y,z]) .&. (f [z,z]))) .&.
                                                                                  (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z])))))))
                                    (generalize davis_putnam_example_formula)),
              TestCase (assertEqual' "meson dp example, step 3 (p. 220)"
                                    ((.~.)(exists "x" (exists "y" (for_all "z" (((f [x,y]) .=>. ((f [y,z]) .&. (f [z,z]))) .&.
                                                                                        (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z]))))))) :: Formula)
                                    ((.~.) (generalize davis_putnam_example_formula))),
              TestCase (assertEqual' "meson dp example, step 4 (p. 220)"
                                    (for_all "x" . for_all "y" $
                                             f[x,y] .&.
                                             ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                             (f[x,y] .&. g[x,y]) .&.
                                             (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]]))))
                                    (runSkolem (askolemize ((.~.) (generalize davis_putnam_example_formula))) :: Formula)),
              TestCase (assertEqual "meson dp example, step 5 (p. 220)"
                                    (Set.map (Set.map prettyShow)
                                     (Set.fromList
                                      [Set.fromList [for_all "x" . for_all "y" $
                                                     f[x,y] .&.
                                                     ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                                     (f[x,y] .&. g[x,y]) .&.
                                                     (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))]]))
{-
[[<<forall x y.
      F(x,y) /\
      (~F(y,f_z(x,y)) \/ ~F(f_z(x,y),f_z(x,y))) \/
      (F(x,y) /\ G(x,y)) /\
      (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y))) >>]]
-}
                                    (Set.map (Set.map prettyShow) (simpdnf' (runSkolem (askolemize ((.~.) (generalize davis_putnam_example_formula))) :: Formula) :: Set (Set Formula)))),
              TestCase (assertEqual "meson dp example, step 6 (p. 220)"
                                    (Set.map prettyShow
                                     (Set.fromList [for_all "x" . for_all "y" $
                                                    f[x,y] .&.
                                                    ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                                    (f[x,y] .&. g[x,y]) .&.
                                                    (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))]))
{-
[<<forall x y.
     F(x,y) /\
     (~F(y,f_z(x,y)) \/ ~F(f_z(x,y),f_z(x,y))) \/
     (F(x,y) /\ G(x,y)) &
     (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y)))>>]
-}
                                    (Set.map prettyShow ((Set.map list_conj (simpdnf' (runSkolem (askolemize ((.~.) (generalize davis_putnam_example_formula)))))) :: Set (Formula))))]
    where f = pApp "F"
          g = pApp "G"
          sk1 = fApp (toSkolem "z" 1)
          x = vt "x"
          y = vt "y"
          z = vt "z"

{-
askolemize (simpdnf (generalize davis_putnam_example_formula)) ->
 <<forall x y. F(x,y) /\ (~F(y,f_z(x,y)) \/ ~F(f_z(x,y), f_z(x,y))) \/ (F(x,y) /\ G(x,y)) /\ (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y)))>>
-}

{-
START_INTERACTIVE;;
tab <<forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))>>;;

tab <<forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))>>;;

-- -------------------------------------------------------------------------
-- The interesting example where tableaux connections make the proof longer.
-- Unfortuntely this gets hammered by normalization first...
-- -------------------------------------------------------------------------

tab <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
      (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
      (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
END_INTERACTIVE;;
-}

-- -------------------------------------------------------------------------
-- Generation of contrapositives.
-- -------------------------------------------------------------------------

contrapositives :: (JustLiteral lit, Ord lit) => Set lit -> Set (PrologRule lit)
contrapositives cls =
    if setAll negative cls then Set.insert (Prolog (Set.map (.~.) cls) false) base else base
    where base = Set.map (\ c -> (Prolog (Set.map (.~.) (Set.delete c cls)) c)) cls

-- -------------------------------------------------------------------------
-- The core of MESON: ancestor unification or Prolog-style extension.
-- -------------------------------------------------------------------------

mexpand1 :: (JustLiteral lit, Ord lit,
             HasApply atom, IsTerm term, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
           Set (PrologRule lit)
        -> Set lit
        -> lit
        -> ((Map v term, Int, Int) -> Failing (Map v term, Int, Int))
        -> (Map v term, Int, Int)
        -> Failing (Map v term, Int, Int)
mexpand1 rules ancestors g cont (env,n,k) =
    if fromEnum n < 0
    then Failure ["Too deep"]
    else case settryfind doAncestor ancestors of
           Success a -> Success a
           Failure _ -> settryfind doRule rules
    where
      doAncestor a =
          do mp <- execStateT (unify_literals g ((.~.) a)) env
             cont (mp, n, k)
      doRule rule =
          do mp <- execStateT (unify_literals g c) env
             mexpand1' (mp, fromEnum n - Set.size asm, k')
          where
            mexpand1' = Set.fold (mexpand1 rules (Set.insert g ancestors)) cont asm
            (Prolog asm c, k') = renamerule k rule

-- -------------------------------------------------------------------------
-- Full MESON procedure.
-- -------------------------------------------------------------------------

puremeson1 :: forall fof atom term v function.
              (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord fof,
               atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term,
               v ~ VarOf fof, v ~ TVarOf term) =>
              Maybe Depth -> fof -> Failing Depth
puremeson1 maxdl fm =
    snd <$> deepen f (Depth 0) maxdl
    where
      f :: Depth -> Failing (Map v term, Int, Int)
      f n = mexpand1 rules (Set.empty :: Set (LFormula atom)) false return (Map.empty, fromEnum n, 0)
      rules = Set.fold (Set.union . contrapositives) Set.empty cls
      (cls :: Set (Set (LFormula atom))) = simpcnf id (specialize id (pnf fm) :: PFormula atom)

meson1 :: forall m fof atom predicate term function v.
          (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord fof, HasSkolem function, Monad m,
           atom ~ AtomOf fof, term ~ TermOf atom, predicate ~ PredOf atom, function ~ FunOf term, v ~ VarOf fof, v ~ SVarOf function) =>
          Maybe Depth -> fof -> SkolemT m function (Set (Failing Depth))
meson1 maxdl fm =
    askolemize ((.~.)(generalize fm)) >>=
    return . Set.map (puremeson1 maxdl . list_conj) . (simpdnf' :: fof -> Set (Set fof))

-- -------------------------------------------------------------------------
-- With repetition checking and divide-and-conquer search.
-- -------------------------------------------------------------------------

equal :: (JustLiteral lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), IsTerm term,
          atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
         Map v term -> lit -> lit -> Bool
equal env fm1 fm2 =
    case execStateT (unify_literals fm1 fm2) env of
      Success env' | env == env' -> True
      _ -> False

expand2 :: (Set lit ->
            ((Map v term, Int, Int) -> Failing (Map v term, Int, Int)) ->
            (Map v term, Int, Int) -> Failing (Map v term, Int, Int))
        -> Set lit
        -> Int
        -> Set lit
        -> Int
        -> Int
        -> ((Map v term, Int, Int) -> Failing (Map v term, Int, Int))
        -> Map v term
        -> Int
        -> Failing (Map v term, Int, Int)
expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
    expfn goals1 (\(e1,r1,k1) ->
                      expfn goals2 (\(e2,r2,k2) ->
                                        if n2 + n1 <= n3 + r2 then Failure ["pair"] else cont (e2,r2,k2))
                                   (e1,n2+r1,k1))
                 (env,n1,k)

mexpand2 :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
           Set (PrologRule lit)
        -> Set lit
        -> lit
        -> ((Map v term, Int, Int) -> Failing (Map v term, Int, Int))
        -> (Map v term, Int, Int)
        -> Failing (Map v term, Int, Int)
mexpand2 rules ancestors g cont (env,n,k) =
    if fromEnum n < 0
    then Failure ["Too deep"]
    else if any (equal env g) ancestors
         then Failure ["repetition"]
         else case settryfind doAncestor ancestors of
                Success a -> Success a
                Failure _ -> settryfind doRule rules
    where
      doAncestor a =
          do mp <- execStateT (unify_literals g ((.~.) a)) env
             cont (mp, n, k)
      doRule rule =
          do mp <- execStateT (unify_literals g c) env
             mexpand2' (mp, fromEnum n - Set.size asm, k')
          where
            mexpand2' = mexpands rules (Set.insert g ancestors) asm cont
            (Prolog asm c, k') = renamerule k rule

mexpands :: (JustLiteral lit, Ord lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), IsTerm term,
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
            Set (PrologRule lit)
         -> Set lit
         -> Set lit
         -> ((Map v term, Int, Int) -> Failing (Map v term, Int, Int))
         -> (Map v term, Int, Int)
         -> Failing (Map v term, Int, Int)
mexpands rules ancestors gs cont (env,n,k) =
    if fromEnum n < 0
    then Failure ["Too deep"]
    else let m = Set.size gs in
         if m <= 1
         then Set.foldr (mexpand2 rules ancestors) cont gs (env,n,k)
         else let n1 = n `div` 2
                  n2 = n - n1 in
              let (goals1, goals2) = setSplitAt (m `div` 2) gs in
              let expfn = expand2 (mexpands rules ancestors) in
              case expfn goals1 n1 goals2 n2 (-1) cont env k of
                Success r -> Success r
                Failure _ -> expfn goals2 n1 goals1 n2 n1 cont env k

setSplitAt :: Ord a => Int -> Set a -> (Set a, Set a)
setSplitAt n s = go n (mempty, s)
    where
      go 0 (s1, s2) = (s1, s2)
      go i (s1, s2) = case Set.minView s2 of
                         Nothing -> (s1, s2)
                         Just (x, s2') -> go (i - 1) (Set.insert x s1, s2')

puremeson2 :: forall fof atom term v.
             (atom ~ AtomOf fof, term ~ TermOf atom, v ~ VarOf fof, v ~ TVarOf term,
              IsFirstOrder fof,
              Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord fof
             ) => Maybe Depth -> fof -> Failing Depth
puremeson2 maxdl fm =
    snd <$> deepen f (Depth 0) maxdl
    where
      f :: Depth -> Failing (Map v term, Int, Int)
      f n = mexpand2 rules (Set.empty :: Set (LFormula atom)) false return (Map.empty, fromEnum n, 0)
      rules = Set.fold (Set.union . contrapositives) Set.empty cls
      (cls :: Set (Set (LFormula atom))) = simpcnf id (specialize id (pnf fm) :: PFormula atom)

meson2 :: forall m fof atom term function v.
          (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord fof,
           HasSkolem function, Monad m,
           atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf fof, v ~ SVarOf function) =>
          Maybe Depth -> fof -> SkolemT m function (Set (Failing Depth))
meson2 maxdl fm =
    askolemize ((.~.)(generalize fm)) >>=
    return . Set.map (puremeson2 maxdl . list_conj) . (simpdnf' :: fof -> Set (Set fof))

meson :: (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), HasSkolem function, Monad m, Ord fof,
          atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf fof, v ~ SVarOf function) =>
         Maybe Depth -> fof -> SkolemT m function (Set (Failing Depth))
meson = meson2

{-
-- -------------------------------------------------------------------------
-- The Los problem (depth 20) and the Steamroller (depth 53) --- lengthier.
-- -------------------------------------------------------------------------

START_INTERACTIVE;;
{- ***********

let los = meson
 <<(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;

let steamroller = meson
 <<((forall x. P1(x) ==> P0(x)) /\ (exists x. P1(x))) /\
   ((forall x. P2(x) ==> P0(x)) /\ (exists x. P2(x))) /\
   ((forall x. P3(x) ==> P0(x)) /\ (exists x. P3(x))) /\
   ((forall x. P4(x) ==> P0(x)) /\ (exists x. P4(x))) /\
   ((forall x. P5(x) ==> P0(x)) /\ (exists x. P5(x))) /\
   ((exists x. Q1(x)) /\ (forall x. Q1(x) ==> Q0(x))) /\
   (forall x. P0(x)
              ==> (forall y. Q0(y) ==> R(x,y)) \/
                  ((forall y. P0(y) /\ S0(y,x) /\
                              (exists z. Q0(z) /\ R(y,z))
                              ==> R(x,y)))) /\
   (forall x y. P3(y) /\ (P5(x) \/ P4(x)) ==> S0(x,y)) /\
   (forall x y. P3(x) /\ P2(y) ==> S0(x,y)) /\
   (forall x y. P2(x) /\ P1(y) ==> S0(x,y)) /\
   (forall x y. P1(x) /\ (P2(y) \/ Q1(y)) ==> ~(R(x,y))) /\
   (forall x y. P3(x) /\ P4(y) ==> R(x,y)) /\
   (forall x y. P3(x) /\ P5(y) ==> ~(R(x,y))) /\
   (forall x. (P4(x) \/ P5(x)) ==> exists y. Q0(y) /\ R(x,y))
   ==> exists x y. P0(x) /\ P0(y) /\
                   exists z. Q1(z) /\ R(y,z) /\ R(x,y)>>;;

*************** -}


-- -------------------------------------------------------------------------
-- Test it.
-- -------------------------------------------------------------------------

let prop_1 = time meson
 <<p ==> q <=> ~q ==> ~p>>;;

let prop_2 = time meson
 <<~ ~p <=> p>>;;

let prop_3 = time meson
 <<~(p ==> q) ==> q ==> p>>;;

let prop_4 = time meson
 <<~p ==> q <=> ~q ==> p>>;;

let prop_5 = time meson
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let prop_6 = time meson
 <<p \/ ~p>>;;

let prop_7 = time meson
 <<p \/ ~ ~ ~p>>;;

let prop_8 = time meson
 <<((p ==> q) ==> p) ==> p>>;;

let prop_9 = time meson
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let prop_10 = time meson
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let prop_11 = time meson
 <<p <=> p>>;;

let prop_12 = time meson
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let prop_13 = time meson
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let prop_14 = time meson
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let prop_15 = time meson
 <<p ==> q <=> ~p \/ q>>;;

let prop_16 = time meson
 <<(p ==> q) \/ (q ==> p)>>;;

let prop_17 = time meson
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

-- -------------------------------------------------------------------------
-- Monadic Predicate Logic.
-- -------------------------------------------------------------------------

let p18 = time meson
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time meson
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time meson
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time meson
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time meson
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time meson
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time meson
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time meson
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time meson
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time meson
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time meson
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time meson
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time meson
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time meson
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time meson
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time meson
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time meson
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time meson
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

-- -------------------------------------------------------------------------
--  Full predicate logic (without Identity and Functions)
-- -------------------------------------------------------------------------

let p36 = time meson
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time meson
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time meson
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time meson
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time meson
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time meson
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time meson
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

let p43 = time meson
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

let p44 = time meson
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

let p45 = time meson
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let p46 = time meson
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

-- -------------------------------------------------------------------------
-- Example from Manthey and Bry, CADE-9.
-- -------------------------------------------------------------------------

let p55 = time meson
 <<lives(agatha) /\ lives(butler) /\ lives(charles) /\
   (killed(agatha,agatha) \/ killed(butler,agatha) \/
    killed(charles,agatha)) /\
   (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
   (hates(agatha,agatha) /\ hates(agatha,charles)) /\
   (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
   (forall x. hates(agatha,x) ==> hates(butler,x)) /\
   (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
   ==> killed(agatha,agatha) /\
       ~killed(butler,agatha) /\
       ~killed(charles,agatha)>>;;

let p57 = time meson
 <<P(f((a),b),f(b,c)) /\
  P(f(b,c),f(a,c)) /\
  (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
  ==> P(f(a,b),f(a,c))>>;;

-- -------------------------------------------------------------------------
-- See info-hol, circa 1500.
-- -------------------------------------------------------------------------

let p58 = time meson
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time meson
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time meson
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

-- -------------------------------------------------------------------------
-- From Gilmore's classic paper.
-- -------------------------------------------------------------------------

{- ** Amazingly, this still seems non-trivial... in HOL it works at depth 45!

let gilmore_1 = time meson
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

 ** -}

{- ** This is not valid, according to Gilmore

let gilmore_2 = time meson
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ** -}

let gilmore_3 = time meson
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time meson
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time meson
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time meson
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time meson
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time meson
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

{- ** This is still a very hard problem

let gilmore_9 = time meson
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

 ** -}

-- -------------------------------------------------------------------------
-- Translation of Gilmore procedure using separate definitions.
-- -------------------------------------------------------------------------

let gilmore_9a = time meson
 <<(forall x y. P(x,y) <=>
                forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
   ==> forall x. exists y. forall z.
             (P(y,x) ==> (P(x,z) ==> P(x,y))) /\
             (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))>>;;

-- -------------------------------------------------------------------------
-- Example from Davis-Putnam papers where Gilmore procedure is poor.
-- -------------------------------------------------------------------------

let davis_putnam_example = time meson
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

-- -------------------------------------------------------------------------
-- The "connections make things worse" example once again.
-- -------------------------------------------------------------------------

meson <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
        (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
        (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
END_INTERACTIVE;;
-}

testMeson :: Test
testMeson = TestLabel "Meson" (TestList [test03, test04, test05, test01, test06, test02])
