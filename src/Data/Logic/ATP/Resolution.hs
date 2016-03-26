-- | Resolution.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Logic.ATP.Resolution
    ( match_atoms
    , match_atoms_eq
    , resolution1
    , resolution2
    , resolution3
    , presolution
    -- , matchAtomsEq
    , davis_putnam_example_formula
    , testResolution
    ) where

import Control.Monad.State (execStateT, get, StateT)
import Data.List as List (map)
import Data.Logic.ATP.Apply (HasApply(TermOf), JustApply, pApp, zipApplys)
import Data.Logic.ATP.Equate (HasEquate, zipEquates)
import Data.Logic.ATP.FOL (generalize, IsFirstOrder, lsubst, var)
import Data.Logic.ATP.Formulas (IsFormula(AtomOf))
import Data.Logic.ATP.Lib (allpairs, allsubsets, allnonemptysubsets, apply, defined,
                           Failing(..), failing, (|->), setAll, setAny, settryfind)
import Data.Logic.ATP.Lit ((.~.), IsLiteral, JustLiteral, LFormula, positive, zipLiterals')
import Data.Logic.ATP.Pretty (assertEqual', Pretty, prettyShow)
import Data.Logic.ATP.Prop ((.|.), (.&.), (.=>.), (.<=>.), list_conj, PFormula, simpcnf, trivial)
import Data.Logic.ATP.Quantified (exists, for_all, IsQuantified(VarOf))
import Data.Logic.ATP.Parser (fof)
import Data.Logic.ATP.Skolem (askolemize, Formula, Function(Skolem), HasSkolem(SVarOf), pnf,
                              runSkolem, simpdnf', SkAtom, skolemize, SkolemT, specialize, SkTerm)
import Data.Logic.ATP.Term (fApp, foldTerm, IsTerm(FunOf, TVarOf), prefix, V, vt)
import Data.Logic.ATP.Unif (solve, Unify(UTermOf), unify_literals)
import Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set as Set
import Data.String (fromString)
import Test.HUnit

-- | Barber's paradox is an example of why we need factoring.
test01 :: Test
test01 = TestCase $ assertEqual ("Barber's paradox: " ++ prettyShow barb ++ " (p. 181)")
                    (prettyShow expected)
                    (prettyShow input)
    where shaves = pApp "shaves" :: [SkTerm] -> Formula
          [b, x] = [vt "b", vt "x"] :: [SkTerm]
          fx = fApp (Skolem "x" 1) :: [SkTerm] -> SkTerm
          barb = exists "b" (for_all "x" (shaves [b, x] .<=>. (.~.)(shaves [x, x]))) :: Formula
          input :: Set (Set (LFormula SkAtom))
          input = simpcnf id (runSkolem (skolemize id ((.~.)barb)) :: PFormula SkAtom)
          -- This is not exactly what is in the book
          expected :: Set (Set Formula)
          expected = Set.fromList [Set.fromList [shaves [b,     fx [b]], (.~.)(shaves [fx [b],fx [b]])],
                                   Set.fromList [shaves [fx [b],fx [b]], (.~.)(shaves [b,     fx [b]])]]
          -- x = vt (fromString "x")
          -- b = vt (fromString "b")
          -- fx = fApp (Skolem "x" 1)

-- | MGU of a set of literals.
mgu :: forall lit atom term v.
       (JustLiteral lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), IsTerm term,
        atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
       Set lit -> StateT (Map v term) Failing (Map v term)
mgu l =
    case Set.minView l of
      Just (a, rest) ->
          case Set.minView rest of
            Just (b, _) -> unify_literals a b >> mgu rest
            _ -> solve <$> get
      _ -> solve <$> get

unifiable :: forall lit term atom v.
             (JustLiteral lit, IsTerm term, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
              atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
             lit -> lit -> Bool
unifiable p q = failing (const False) (const True) (execStateT (unify_literals p q) Map.empty :: Failing (Map v term))

-- -------------------------------------------------------------------------
-- Rename a clause.
-- -------------------------------------------------------------------------

rename :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term,
           atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
          (v -> v) -> Set lit -> Set lit
rename pfx cls =
    Set.map (lsubst (Map.fromList (Set.toList (Set.map (\v -> (v, (vt (pfx v)))) fvs)))) cls
    where
      fvs = Set.fold Set.union Set.empty (Set.map var cls)

-- -------------------------------------------------------------------------
-- General resolution rule, incorporating factoring as in Robinson's paper.
-- -------------------------------------------------------------------------

resolvents :: (JustLiteral lit, Ord lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), IsTerm term,
               atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
              Set lit -> Set lit -> lit -> Set lit -> Set lit
resolvents cl1 cl2 p acc =
    if Set.null ps2 then acc else Set.fold doPair acc pairs
    where
      doPair (s1,s2) sof =
          case execStateT (mgu (Set.union s1 (Set.map (.~.) s2))) Map.empty of
            Success mp -> Set.union (Set.map (lsubst mp) (Set.union (Set.difference cl1 s1) (Set.difference cl2 s2))) sof
            Failure _ -> sof
      -- pairs :: Set (Set fof, Set fof)
      pairs = allpairs (,) (Set.map (Set.insert p) (allsubsets ps1)) (allnonemptysubsets ps2)
      -- ps1 :: Set fof
      ps1 = Set.filter (\ q -> q /= p && unifiable p q) cl1
      -- ps2 :: Set fof
      ps2 = Set.filter (unifiable ((.~.) p)) cl2

resolve_clauses :: (JustLiteral lit, Ord lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), IsTerm term,
                    atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                   Set lit -> Set lit -> Set lit
resolve_clauses cls1 cls2 =
    let cls1' = rename (prefix "x") cls1
        cls2' = rename (prefix "y") cls2 in
    Set.fold (resolvents cls1' cls2') Set.empty cls1'

-- -------------------------------------------------------------------------
-- Basic "Argonne" loop.
-- -------------------------------------------------------------------------

resloop1 :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
            Set (Set lit) -> Set (Set lit) -> Failing Bool
resloop1 used unused =
    maybe (Failure ["No proof found"]) step (Set.minView unused)
    where
      step (cl, ros) =
          if Set.member Set.empty news then return True else resloop1 used' (Set.union ros news)
          where
            used' = Set.insert cl used
            -- resolve_clauses is not in the Failing monad, so setmapfilter isn't appropriate.
            news = Set.fold Set.insert Set.empty ({-setmapfilter-} Set.map (resolve_clauses cl) used')

pure_resolution1 :: forall fof atom term v.
                    (atom ~ AtomOf fof, term ~ TermOf atom, v ~ TVarOf term,
                     IsFirstOrder fof,
                     Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
                     Ord fof, Pretty fof
                    ) => fof -> Failing Bool
pure_resolution1 fm = resloop1 Set.empty (simpcnf id (specialize id (pnf fm) :: PFormula atom) :: Set (Set (LFormula atom)))

resolution1 :: forall m fof atom term v function.
               (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord fof, HasSkolem function, Monad m,
                atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function) =>
               fof -> SkolemT m function (Set (Failing Bool))
resolution1 fm = askolemize ((.~.)(generalize fm)) >>= return . Set.map (pure_resolution1 . list_conj) . (simpdnf' :: fof -> Set (Set fof))

-- | Simple example that works well.
davis_putnam_example_formula :: Formula
davis_putnam_example_formula = [fof| ∃ x y. (∀ z. ((F(x,y)⇒F(y,z)∧F(z,z))∧(F(x,y)∧G(x,y)⇒G(x,z)∧G(z,z)))) |]
{-
    exists "x" . exists "y" .for_all "z" $
              (f [x, y] .=>. (f [y, z] .&. f [z, z])) .&.
              ((f [x, y] .&. g [x, y]) .=>. (g [x, z] .&. g [z, z]))
    where
      [x, y, z] = [vt "x", vt "y", vt "z"] :: [SkTerm]
      [g, f] = [pApp "G", pApp "F"] :: [[SkTerm] -> Formula]
-}
test02 :: Test
test02 =
    TestCase $ assertEqual "Davis-Putnam example 1" expected (runSkolem (resolution1 davis_putnam_example_formula))
        where
          expected = Set.singleton (Success True)

-- -------------------------------------------------------------------------
-- Matching of terms and literals.
-- -------------------------------------------------------------------------

class Match a v term where
    match :: Map v term -> a -> Failing (Map v term)

match_terms :: forall term v. (IsTerm term, v ~ TVarOf term) => Map v term -> [(term, term)] -> Failing (Map v term)
match_terms env [] = Success env
match_terms env ((p, q) : oth) =
    foldTerm vr fn p
    where
      vr x | not (defined env x) = match_terms ((x |-> q) env) oth
           | apply env x == Just q = match_terms env oth
           | otherwise = fail "match_terms"
      fn f fa =
          foldTerm vr' fn' q
          where
            fn' g ga | f == g && length fa == length ga = match_terms env (zip fa ga ++ oth)
            fn' _ _ = fail "match_terms"
            vr' _ = fail "match_terms"

match_atoms :: (JustApply atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) =>
               Map v term -> (atom, atom) -> Failing (Map v term)
match_atoms env (a1, a2) =
    maybe (Failure ["match_atoms"]) id (zipApplys (\_ pairs -> Just (match_terms env pairs)) a1 a2)

match_atoms_eq :: (HasEquate atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) =>
                  Map v term -> (atom, atom) -> Failing (Map v term)
match_atoms_eq env (a1, a2) =
    maybe (Failure ["match_atoms_eq"]) id (zipEquates (\l1 r1 l2 r2 -> Just (match_terms env [(l1, l2), (r1, r2)]))
                                                      (\_ pairs -> Just (match_terms env pairs)) a1 a2)

match_literals :: forall lit atom term v.
                  (IsLiteral lit, HasApply atom, IsTerm term, Match (atom, atom) v term,
                   atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                  Map v term -> lit -> lit -> Failing (Map v term)
match_literals env t1 t2 =
    fromMaybe (fail "match_literals") (zipLiterals' ho ne tf at t1 t2)
    where
      ho _ _ = Nothing
      ne p q = Just $ match_literals env p q
      tf a b = if a == b then Just (Success env) else Nothing
      at a1 a2 = Just (match env (a1, a2))

-- | With deletion of tautologies and bi-subsumption with "unused".
resolution2 :: forall fof atom term v function m.
               (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term, HasSkolem function, Monad m, Ord fof,
                atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function) =>
               fof -> SkolemT m function (Set (Failing Bool))
resolution2 fm = askolemize ((.~.) (generalize fm)) >>= return . Set.map (pure_resolution2 . list_conj) . (simpdnf' :: fof -> Set (Set fof))

pure_resolution2 :: forall fof atom term v.
                    (IsFirstOrder fof, Ord fof, Pretty fof,
                     HasApply atom, IsTerm term,
                     Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term,
                     atom ~ AtomOf fof, term ~ TermOf atom, v ~ TVarOf term) =>
                    fof -> Failing Bool
pure_resolution2 fm = resloop2 Set.empty (simpcnf id (specialize id (pnf fm) :: PFormula atom) :: Set (Set (LFormula atom)))

resloop2 :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term,
             Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term,
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
            Set (Set lit) -> Set (Set lit) -> Failing Bool
resloop2 used unused =
    case Set.minView unused of
      Nothing -> Failure ["No proof found"]
      Just (cl, ros) ->
          -- print_string(string_of_int(length used) ^ " used; "^ string_of_int(length unused) ^ " unused.");
          -- print_newline();
          let used' = Set.insert cl used in
          let news = Set.map (resolve_clauses cl) used' in
          if Set.member Set.empty news then return True else resloop2 used' (Set.fold (incorporate cl) ros news)

incorporate :: (atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term,
                IsLiteral lit, Ord lit,
                HasApply atom, Match (atom, atom) v term,
                IsTerm term) =>
               Set lit
            -> Set lit
            -> Set (Set lit)
            -> Set (Set lit)
incorporate gcl cl unused =
    if trivial cl || setAny (\ c -> subsumes_clause c cl) (Set.insert gcl unused)
    then unused
    else replace cl unused

replace :: (atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term,
            IsLiteral lit, Ord lit,
            IsTerm term,
            HasApply atom, Match (atom, atom) v term) =>
           Set lit
        -> Set (Set lit)
        -> Set (Set lit)
replace cl st =
    case Set.minView st of
      Nothing -> Set.singleton cl
      Just (c, st') -> if subsumes_clause cl c
                       then Set.insert cl st'
                       else Set.insert c (replace cl st')

-- | Test for subsumption
subsumes_clause :: (IsLiteral lit, HasApply atom, IsTerm term, Match (atom, atom) v term,
                    atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                   Set lit -> Set lit -> Bool
subsumes_clause cls1 cls2 =
    failing (const False) (const True) (subsume Map.empty cls1)
    where
      subsume env cls =
          case Set.minView cls of
            Nothing -> Success env
            Just (l1, clt) -> settryfind (\ l2 -> case (match_literals env l1 l2) of
                                                    Success env' -> subsume env' clt
                                                    Failure msgs -> Failure msgs) cls2

test03 :: Test
test03 = TestCase $ assertEqual' "Davis-Putnam example 2" expected (runSkolem (resolution2 davis_putnam_example_formula))
        where
          expected = Set.singleton (Success True)

-- | Positive (P1) resolution.
presolution :: forall fof atom term v function m.
               (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term, HasSkolem function, Monad m, Ord fof, Pretty fof,
                atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf fof, v ~ SVarOf function) =>
               fof -> SkolemT m function (Set (Failing Bool))
presolution fm =
    askolemize ((.~.) (generalize fm)) >>= return . Set.map (pure_presolution . list_conj) . (simpdnf' :: fof -> Set (Set fof))

pure_presolution :: forall fof atom term v.
                    (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term, Ord fof, Pretty fof,
                     atom ~ AtomOf fof, term ~ TermOf atom, v ~ VarOf fof, v ~ TVarOf term) =>
                    fof -> Failing Bool
pure_presolution fm = presloop Set.empty (simpcnf id (specialize id (pnf fm :: fof) ::  PFormula atom) :: Set (Set (LFormula atom)))

presloop :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term,
             Match (atom, atom) v term, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
             atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
            Set (Set lit) -> Set (Set lit) -> Failing Bool
presloop used unused =
    case Set.minView unused of
      Nothing -> Failure ["No proof found"]
      Just (cl, ros) ->
          -- print_string(string_of_int(length used) ^ " used; "^ string_of_int(length unused) ^ " unused.");
          -- print_newline();
          let used' = Set.insert cl used in
          let news = Set.map (presolve_clauses cl) used' in
          if Set.member Set.empty news
          then Success True
          else presloop used' (Set.fold (incorporate cl) ros news)

presolve_clauses :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
                     atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                    Set lit -> Set lit -> Set lit
presolve_clauses cls1 cls2 =
    if setAll positive cls1 || setAll positive cls2
    then resolve_clauses cls1 cls2
    else Set.empty

-- | Introduce a set-of-support restriction.
resolution3 :: forall fof atom term v function m.
               (IsFirstOrder fof, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Match (atom, atom) v term, HasSkolem function, Monad m, Ord fof,
                atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf fof, v ~ SVarOf function) =>
               fof -> SkolemT m function (Set (Failing Bool))
resolution3 fm =
    askolemize ((.~.)(generalize fm)) >>= return . Set.map (pure_resolution3 . list_conj) . (simpdnf' :: fof -> Set (Set fof))

pure_resolution3 :: forall fof atom term v.
                    (atom ~ AtomOf fof, term ~ TermOf atom, v ~ VarOf fof, v ~ TVarOf term,
                     IsFirstOrder fof,
                     Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
                     Match (atom, atom) v term,
                     Ord fof, Pretty fof) => fof -> Failing Bool
pure_resolution3 fm =
    uncurry resloop2 (Set.partition (setAny positive) (simpcnf id (specialize id (pnf fm) :: PFormula atom) :: Set (Set (LFormula atom))))

instance Match (SkAtom, SkAtom) V SkTerm where
    match = match_atoms_eq


gilmore_1 :: Test
gilmore_1 = TestCase $ assertEqual "Gilmore 1" expected (runSkolem (resolution3 fm))
    where
      expected = Set.singleton (Success True)
      fm :: Formula
      fm = exists "x" . for_all "y" . for_all "z" $
           ((f[y] .=>. g[y]) .<=>. f[x]) .&.
           ((f[y] .=>. h[y]) .<=>. g[x]) .&.
           (((f[y] .=>. g[y]) .=>. h[y]) .<=>. h[x])
           .=>. f[z] .&. g[z] .&. h[z]
      [x, y, z] = [vt "x", vt "y", vt "z"] :: [SkTerm]
      [f, g, h] = [pApp "F", pApp "G", pApp "H"]

-- The Pelletier examples again.
p1 :: Test
p1 =
    let [p, q] = [pApp (fromString "p") [], pApp (fromString "q") []] :: [Formula] in
    TestCase $ assertEqual "p1" Set.empty (runSkolem (presolution ((p .=>. q .<=>. (.~.)q .=>. (.~.)p) :: Formula)))

{-
-- -------------------------------------------------------------------------
-- The Pelletier examples again.
-- -------------------------------------------------------------------------

{- **********

let p1 = time presolution
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time presolution
 <<~ ~p <=> p>>;;

let p3 = time presolution
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time presolution
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time presolution
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time presolution
 <<p \/ ~p>>;;

let p7 = time presolution
 <<p \/ ~ ~ ~p>>;;

let p8 = time presolution
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time presolution
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time presolution
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time presolution
 <<p <=> p>>;;

let p12 = time presolution
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time presolution
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time presolution
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time presolution
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time presolution
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time presolution
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

-- -------------------------------------------------------------------------
-- Monadic Predicate Logic.
-- -------------------------------------------------------------------------

let p18 = time presolution
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time presolution
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time presolution
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = time presolution
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time presolution
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time presolution
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time presolution
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time presolution
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time presolution
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time presolution
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time presolution
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time presolution
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time presolution
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\
   (forall x. (G(x) ==> ~U(x)) ==> P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time presolution
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time presolution
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time presolution
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time presolution
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time presolution
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

-- -------------------------------------------------------------------------
--  Full predicate logic (without Identity and Functions)
-- -------------------------------------------------------------------------

let p36 = time presolution
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time presolution
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

{- ** This one seems too slow

let p38 = time presolution
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

 ** -}

let p39 = time presolution
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time presolution
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time presolution
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

{- ** Also very slow

let p42 = time presolution
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

 ** -}

{- ** and this one too..

let p43 = time presolution
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

 ** -}

let p44 = time presolution
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

{- ** and this...

let p45 = time presolution
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

 ** -}

{- ** and this

let p46 = time presolution
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

 ** -}

-- -------------------------------------------------------------------------
-- Example from Manthey and Bry, CADE-9.
-- -------------------------------------------------------------------------

let p55 = time presolution
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

let p57 = time presolution
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

-- -------------------------------------------------------------------------
-- See info-hol, circa 1500.
-- -------------------------------------------------------------------------

let p58 = time presolution
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time presolution
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time presolution
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

-- -------------------------------------------------------------------------
-- From Gilmore's classic paper.
-- -------------------------------------------------------------------------

let gilmore_1 = time presolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

{- ** This is not valid, according to Gilmore

let gilmore_2 = time presolution
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ** -}

let gilmore_3 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time presolution
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time presolution
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time presolution
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time presolution
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

{- ** This one still isn't easy!

let gilmore_9 = time presolution
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
-- Example from Davis-Putnam papers where Gilmore procedure is poor.
-- -------------------------------------------------------------------------

let davis_putnam_example = time presolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

*********** -}
END_INTERACTIVE;;

-- -------------------------------------------------------------------------
-- Example
-- -------------------------------------------------------------------------

START_INTERACTIVE;;
let gilmore_1 = resolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

-- -------------------------------------------------------------------------
-- Pelletiers yet again.
-- -------------------------------------------------------------------------

{- ************

let p1 = time resolution
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time resolution
 <<~ ~p <=> p>>;;

let p3 = time resolution
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time resolution
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time resolution
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time resolution
 <<p \/ ~p>>;;

let p7 = time resolution
 <<p \/ ~ ~ ~p>>;;

let p8 = time resolution
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time resolution
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time resolution
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time resolution
 <<p <=> p>>;;

let p12 = time resolution
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time resolution
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time resolution
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time resolution
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time resolution
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time resolution
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let p18 = time resolution
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time resolution
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time resolution
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time resolution
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))>>;;

let p22 = time resolution
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time resolution
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time resolution
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time resolution
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time resolution
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time resolution
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time resolution
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time resolution
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time resolution
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time resolution
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time resolution
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time resolution
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time resolution
 <<((exists x. forall y. P(x) <=> P(y)) <=>
   ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
  ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time resolution
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(*  Full predicate logic (without Identity and Functions)                    *)
(* ------------------------------------------------------------------------- *)

let p36 = time resolution
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time resolution
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

(*** This one seems too slow

let p38 = time resolution
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

 ***)

let p39 = time resolution
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time resolution
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time resolution
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

(*** Also very slow

let p42 = time resolution
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

 ***)

(*** and this one too..

let p43 = time resolution
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

 ***)

let p44 = time resolution
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

(*** and this...

let p45 = time resolution
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

 ***)

(*** and this

let p46 = time resolution
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time resolution
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

let p57 = time resolution
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* See info-hol, circa 1500.                                                 *)
(* ------------------------------------------------------------------------- *)

let p58 = time resolution
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p59 = time resolution
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = time resolution
 <<forall x. P(x,f(x)) <=>
            exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

(* ------------------------------------------------------------------------- *)
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time resolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

(*** This is not valid, according to Gilmore

let gilmore_2 = time resolution
 <<exists x y. forall z.
        (F(x,z) <=> F(z,y)) /\ (F(z,y) <=> F(z,z)) /\ (F(x,y) <=> F(y,x))
        ==> (F(x,y) <=> F(x,z))>>;;

 ***)

let gilmore_3 = time resolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time resolution
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time resolution
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time resolution
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time resolution
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time resolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

(*** This one still isn't easy!

let gilmore_9 = time resolution
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
-}
-}

-- | The (in)famous Los problem.
los :: Test
los =
    let [x, y, z] = List.map (vt :: V -> SkTerm) ["x", "y", "z"]
        [p, q] = List.map pApp ["P", "Q"] :: [[SkTerm] -> Formula]
        fm = (for_all "x" $ for_all "y" $ for_all "z" $ p[x,y] .=>. p[y,z] .=>. p[x,z]) .&.
             (for_all "x" $ for_all "y" $ for_all "z" $ q[x,y] .=>. q[y,z] .=>. q[x,z]) .&.
             (for_all "x" $ for_all "y" $ q[x,y] .=>. q[y,x]) .&.
             (for_all "x" $ for_all "y" $ p[x,y] .|. q[x,y])
             .=>. (for_all "x" $ for_all "y" $ p[x,y]) .|. (for_all "x" $ for_all "y" $ q[x,y]) :: Formula
        result = {-time-} runSkolem (presolution fm)
        expected = Set.singleton (Success True) in
    TestCase $ assertEqual "los (p. 198)" expected result

testResolution :: Test
testResolution = TestLabel "Resolution" (TestList [test01, test02, test03, gilmore_1, p1, los])
