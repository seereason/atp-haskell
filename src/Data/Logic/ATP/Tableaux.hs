-- | Tableaux, seen as an optimized version of a Prawitz-like procedure.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Data.Logic.ATP.Tableaux
    ( prawitz
    , K(K)
    , tab
    , testTableaux
    ) where

import Data.Logic.ATP.Apply (HasApply(TermOf), pApp)
import Control.Monad.RWS (RWS)
import Control.Monad.State (execStateT, StateT)
import Data.List as List (map)
import Data.Logic.ATP.FOL (asubst, fv, generalize, IsFirstOrder, subst)
import Data.Logic.ATP.Formulas (atomic, IsFormula(asBool, AtomOf), onatoms, overatoms)
import Data.Logic.ATP.Herbrand (davisputnam)
import Data.Logic.ATP.Lib ((|=>), allpairs, deepen, Depth(Depth), distrib, evalRS, Failing(Success, Failure), failing, settryfind, tryfindM)
import Data.Logic.ATP.Lit ((.~.), convertToLiteral, IsLiteral, JustLiteral, LFormula, positive)
import Data.Logic.ATP.LitWrapper (JL)
import Data.Logic.ATP.Pretty (assertEqual', Pretty(pPrint), prettyShow, text)
import Data.Logic.ATP.Prop ( (.&.), (.=>.), (.<=>.), (.|.), BinOp((:&:), (:|:)), PFormula, simpdnf)
import Data.Logic.ATP.Quantified (exists, foldQuantified, for_all, Quant((:!:)))
import Data.Logic.ATP.Skolem (askolemize, Formula, HasSkolem(SVarOf, toSkolem), runSkolem, simpdnf', skolemize, SkTerm)
import Data.Logic.ATP.Term (fApp, IsTerm(TVarOf, FunOf), vt)
import Data.Logic.ATP.Unif (Unify(UTermOf), unify_literals)
import Data.Map.Strict as Map
import Data.Set as Set
import Data.String (IsString(..))
import Prelude hiding (compare)
import Test.HUnit hiding (State)

-- | Unify complementary literals.
unify_complements :: (IsLiteral lit1, JustLiteral lit2, HasApply atom1, HasApply atom2,
                      Unify m (atom1, atom2), term ~ UTermOf (atom1, atom2), v ~ TVarOf term,
                      atom1 ~ AtomOf lit1, term ~ TermOf atom1,
                      atom2 ~ AtomOf lit2, term ~ TermOf atom2) =>
                     lit1 -> lit2 -> StateT (Map v term) m ()
unify_complements p q = unify_literals p ((.~.) q)

-- | Unify and refute a set of disjuncts.
unify_refute :: (JustLiteral lit, Ord lit, HasApply atom, IsTerm term,
                 Unify Failing (atom, atom), term ~ UTermOf (atom, atom), v ~ TVarOf term,
                 atom ~ AtomOf lit, term ~ TermOf atom) =>
                Set (Set lit) -> Map v term -> Failing (Map v term)
unify_refute djs env =
    case Set.minView djs of
      Nothing -> pure env
      Just (d, odjs) ->
          settryfind (\ (p, n) -> execStateT (unify_complements p n) env >>= unify_refute odjs) pairs
          where
            pairs = allpairs (,) pos neg
            (pos,neg) = Set.partition positive d

-- | Hence a Prawitz-like procedure (using unification on DNF).
prawitz_loop :: forall lit atom v term.
                (JustLiteral lit, Ord lit, HasApply atom, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
                 atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                Set (Set lit) -> [v] -> Set (Set lit) -> Int -> (Map v term, Int)
prawitz_loop djs0 fvs djs n =
    let inst = Map.fromList (zip fvs (List.map newvar [1..]))
        djs1 = distrib (Set.map (Set.map (onatoms (asubst inst))) djs0) djs in
    case unify_refute djs1 Map.empty of
      Failure _ -> prawitz_loop djs0 fvs djs1 (n + 1)
      Success env -> (env, n + 1)
    where
      newvar k = vt (fromString ("_" ++ show (n * length fvs + k)))

prawitz :: forall formula atom term function v.
           (IsFirstOrder formula, Ord formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), HasSkolem function, Show formula,
            atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
            v ~ TVarOf term, v ~ SVarOf function) =>
           formula -> Int
prawitz fm =
    snd (prawitz_loop dnf (Set.toList fvs) dnf0 0)
    where
      dnf0 = Set.singleton Set.empty
      dnf = (simpdnf id pf :: Set (Set (LFormula atom)))
      fvs = overatoms (\ a s -> Set.union (fv (atomic a :: formula)) s) pf (Set.empty :: Set v)
      pf = runSkolem (skolemize id ((.~.)(generalize fm))) :: PFormula atom

-- -------------------------------------------------------------------------
-- Examples.
-- -------------------------------------------------------------------------

p20 :: Test
p20 = TestCase $ assertEqual' "p20 - prawitz (p. 175)" expected input
    where fm :: Formula
          fm = (for_all "x" (for_all "y" (exists "z" (for_all "w" (pApp "P" [vt "x"] .&. pApp "Q" [vt "y"] .=>.
                                                                   pApp "R" [vt "z"] .&. pApp "U" [vt "w"]))))) .=>.
               (exists "x" (exists "y" (pApp "P" [vt "x"] .&. pApp "Q" [vt "y"]))) .=>. (exists "z" (pApp "R" [vt "z"]))
          input = prawitz fm
          expected = 2

-- -------------------------------------------------------------------------
-- Comparison of number of ground instances.
-- -------------------------------------------------------------------------

compare :: (IsFirstOrder formula, Ord formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), HasSkolem function, Show formula,
            atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
            v ~ TVarOf term, v ~ SVarOf function) =>
           formula -> (Int, Int)
compare fm = (prawitz fm, davisputnam fm)

p19 :: Test
p19 = TestCase $ assertEqual' "p19" expected input
    where
      fm :: Formula
      fm = exists "x" (for_all "y" (for_all "z" ((pApp "P" [vt "y"] .=>. pApp "Q" [vt "z"]) .=>. pApp "P" [vt "x"] .=>. pApp "Q" [vt "x"])))
      input = compare fm
      expected = (3, 3)

{-
START_INTERACTIVE;;
let p20 = compare
 <<(for_all x y. exists z. for_all w. P[vt "x"] .&. Q[vt "y"] .=>. R[vt "z"] .&. U[vt "w"])
   .=>. (exists x y. P[vt "x"] .&. Q[vt "y"]) .=>. (exists z. R[vt "z"])>>;;

let p24 = compare
 <<~(exists x. U[vt "x"] .&. Q[vt "x"]) .&.
   (for_all x. P[vt "x"] .=>. Q[vt "x"] .|. R[vt "x"]) .&.
   ~(exists x. P[vt "x"] .=>. (exists x. Q[vt "x"])) .&.
   (for_all x. Q[vt "x"] .&. R[vt "x"] .=>. U[vt "x"])
   .=>. (exists x. P[vt "x"] .&. R[vt "x"])>>;;

let p39 = compare
 <<~(exists x. for_all y. P(y,x) .<=>. ~P(y,y))>>;;

let p42 = compare
 <<~(exists y. for_all x. P(x,y) .<=>. ~(exists z. P(x,z) .&. P(z,x)))>>;;

{- **** Too slow?

let p43 = compare
 <<(for_all x y. Q(x,y) .<=>. for_all z. P(z,x) .<=>. P(z,y))
   .=>. for_all x y. Q(x,y) .<=>. Q(y,x)>>;;

 ***** -}

let p44 = compare
 <<(for_all x. P[vt "x"] .=>. (exists y. G[vt "y"] .&. H(x,y)) .&.
   (exists y. G[vt "y"] .&. ~H(x,y))) .&.
   (exists x. J[vt "x"] .&. (for_all y. G[vt "y"] .=>. H(x,y)))
   .=>. (exists x. J[vt "x"] .&. ~P[vt "x"])>>;;

let p59 = compare
 <<(for_all x. P[vt "x"] .<=>. ~P(f[vt "x"])) .=>. (exists x. P[vt "x"] .&. ~P(f[vt "x"]))>>;;

let p60 = compare
 <<for_all x. P(x,f[vt "x"]) .<=>.
             exists y. (for_all z. P(z,y) .=>. P(z,f[vt "x"])) .&. P(x,y)>>;;

END_INTERACTIVE;;
-}

newtype K = K Int deriving (Eq, Ord, Show)

instance Enum K where
    toEnum = K
    fromEnum (K n) = n

instance Pretty K where
    pPrint (K n) = text ("K" ++ show n)

-- | More standard tableau procedure, effectively doing DNF incrementally.  (p. 177)
tableau :: forall formula atom term v function.
           (IsFirstOrder formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
            atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term) =>
           [formula] -> Depth -> RWS () () () (Failing (K, Map v term))
tableau fms n0 =
    go (fms, [], n0) (return . Success) (K 0, Map.empty)
    where
      go :: ([formula], [JL formula], Depth)
         -> ((K, Map v term) -> RWS () () () (Failing (K, Map v term)))
         -> (K, Map v term)
         -> RWS () () () (Failing (K, Map v term))
      go (_, _, n) _ (_, _) | n < Depth 0 = return $ Failure ["no proof at this level"]
      go ([], _, _) _ (_, _) =  return $ Failure ["tableau: no proof"]
      go (fm : unexp, lits, n) cont (k, env) =
          foldQuantified qu co (\_ -> go2 fm unexp) (\_ -> go2 fm unexp) (\_ -> go2 fm unexp) fm
          where
            qu :: Quant -> v -> formula -> RWS () () () (Failing (K, Map v term))
            qu (:!:) x p =
                let y = vt (fromString (prettyShow k))
                    p' = subst (x |=> y) p in
                go ([p'] ++ unexp ++ [for_all x p],lits,pred n) cont (succ k, env)
            qu _ _ _ = go2 fm unexp
            co p (:&:) q =
                go (p : q : unexp,lits,n) cont (k, env)
            co p (:|:) q =
                go (p : unexp,lits,n) (go (q : unexp,lits,n) cont) (k, env)
            co _ _ _ = go2 fm unexp

            go2 :: formula -> [formula] -> RWS () () () (Failing (K, Map v term))
            go2 fm' unexp' =
                let (fm'' :: JL formula) = convertToLiteral (error "expected JustLiteral") id fm' in
                tryfindM (tryLit fm'') lits >>=
                failing (\_ -> go (unexp', fm'' : lits, n) cont (k, env))
                        (return . Success)
            tryLit :: JL formula -> JL formula -> RWS () () () (Failing (K, Map v term))
            tryLit fm' l = failing (return . Failure) (\env' -> cont (k, env')) (execStateT (unify_complements fm' l) env)

tabrefute :: (IsFirstOrder formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom),
              atom ~ AtomOf formula, term ~ TermOf atom, v ~ TVarOf term) =>
             Maybe Depth -> [formula] -> Failing ((K, Map v term), Depth)
tabrefute limit fms =
    let r = deepen (\n -> (,n) <$> evalRS (tableau fms n) () ()) (Depth 0) limit in
    failing Failure (Success . fst) r

tab :: (IsFirstOrder formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Pretty formula, HasSkolem function,
        atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
        v ~ TVarOf term, v ~ SVarOf function) =>
       Maybe Depth -> formula -> Failing ((K, Map v term), Depth)
tab limit fm =
  let sfm = runSkolem (askolemize((.~.)(generalize fm))) in
  if asBool sfm == Just False then (error "Tableaux.tab") else tabrefute limit [sfm]

p38 :: Test
p38 =
    let [p, r] = [pApp "P", pApp "R"] :: [[SkTerm] -> Formula]
        [a, w, x, y, z] = [vt "a", vt "w", vt "x", vt "y", vt "z"] :: [SkTerm]
        fm = (for_all "x"
               (p[a] .&. (p[x] .=>. (exists "y" (p[y] .&. r[x,y]))) .=>.
                (exists "z" (exists "w" (p[z] .&. r[x,w] .&. r[w,z]))))) .<=>.
             (for_all "x"
              (((.~.)(p[a]) .|. p[x] .|. (exists "z" (exists "w" (p[z] .&. r[x,w] .&. r[w,z])))) .&.
               ((.~.)(p[a]) .|. (.~.)(exists "y" (p[y] .&. r[x,y])) .|.
               (exists "z" (exists "w" (p[z] .&. r[x,w] .&. r[w,z]))))))
        expected = Success ((K 22,
                             Map.fromList
                                      [("K0",fApp ((toSkolem "x" 1))[]),
                                       ("K1",fApp ((toSkolem "y" 1))[]),
                                       ("K10",fApp ((toSkolem "x" 2))[]),
                                       ("K11",fApp ((toSkolem "z" 3))["K13"]),
                                       ("K12",fApp ((toSkolem "w" 3))["K16"]),
                                       ("K13",fApp ((toSkolem "x" 2))[]),
                                       ("K14",fApp ((toSkolem "y" 2))[]),
                                       ("K15",fApp ((toSkolem "y" 2))[]),
                                       ("K16",fApp ((toSkolem "x" 2))[]),
                                       ("K17",fApp ((toSkolem "y" 2))[]),
                                       ("K18",fApp ((toSkolem "y" 2))[]),
                                       ("K19",fApp ((toSkolem "x" 2))[]),
                                       ("K2",fApp ((toSkolem "z" 1))["K0"]),
                                       ("K20",fApp ((toSkolem "y" 2))[]),
                                       ("K21",fApp ((toSkolem "y" 2))[]),
                                       ("K3",fApp ((toSkolem "w" 1))["K0"]),
                                       ("K4",fApp ((toSkolem "z" 1))["K0"]),
                                       ("K5",fApp ((toSkolem "w" 1))["K0"]),
                                       ("K6",fApp ((toSkolem "z" 2))["K8"]),
                                       ("K7",fApp ((toSkolem "w" 2))["K9"]),
                                       ("K8",fApp ((toSkolem "x" 2))[]),
                                       ("K9",fApp ((toSkolem "x" 2))[])]
                                      ),
                            Depth 4) in
    TestCase $ assertEqual' "p38, p. 178" expected (tab Nothing fm)
{-
-- -------------------------------------------------------------------------
-- Example.
-- -------------------------------------------------------------------------

START_INTERACTIVE;;
let p38 = tab
 <<(for_all x.
     P[vt "a"] .&. (P[vt "x"] .=>. (exists y. P[vt "y"] .&. R(x,y))) .=>.
     (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))) .<=>.
   (for_all x.
     (~P[vt "a"] .|. P[vt "x"] .|. (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))) .&.
     (~P[vt "a"] .|. ~(exists y. P[vt "y"] .&. R(x,y)) .|.
     (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))))>>;;
END_INTERACTIVE;;
-}

-- -------------------------------------------------------------------------
-- Try to split up the initial formula first; often a big improvement.
-- -------------------------------------------------------------------------
splittab :: forall formula atom term v function.
            (IsFirstOrder formula, Unify Failing (atom, atom), term ~ UTermOf (atom, atom), Ord formula, Pretty formula, HasSkolem function,
             atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
             v ~ TVarOf term, v ~ SVarOf function) =>
            formula -> [Failing ((K, Map v term), Depth)]
splittab fm =
    (List.map (tabrefute Nothing) . ssll . simpdnf' . runSkolem . askolemize . (.~.) . generalize) fm
    where ssll = List.map Set.toList . Set.toList
          -- simpdnf' :: PFormula atom -> Set (Set (LFormula atom))
          -- simpdnf' = simpdnf id

{-
-- -------------------------------------------------------------------------
-- Example: the Andrews challenge.
-- -------------------------------------------------------------------------

START_INTERACTIVE;;
let p34 = splittab
 <<((exists x. for_all y. P[vt "x"] .<=>. P[vt "y"]) .<=>.
    ((exists x. Q[vt "x"]) .<=>. (for_all y. Q[vt "y"]))) .<=>.
   ((exists x. for_all y. Q[vt "x"] .<=>. Q[vt "y"]) .<=>.
    ((exists x. P[vt "x"]) .<=>. (for_all y. P[vt "y"])))>>;;

-- -------------------------------------------------------------------------
-- Another nice example from EWD 1602.
-- -------------------------------------------------------------------------

let ewd1062 = splittab
 <<(for_all x. x <= x) .&.
   (for_all x y z. x <= y .&. y <= z .=>. x <= z) .&.
   (for_all x y. f[vt "x"] <= y .<=>. x <= g[vt "y"])
   .=>. (for_all x y. x <= y .=>. f[vt "x"] <= f[vt "y"]) .&.
       (for_all x y. x <= y .=>. g[vt "x"] <= g[vt "y"])>>;;
END_INTERACTIVE;;

-- -------------------------------------------------------------------------
-- Do all the equality-free Pelletier problems, and more, as examples.
-- -------------------------------------------------------------------------

{- **********

let p1 = time splittab
 <<p .=>. q .<=>. ~q .=>. ~p>>;;

let p2 = time splittab
 <<~ ~p .<=>. p>>;;

let p3 = time splittab
 <<~(p .=>. q) .=>. q .=>. p>>;;

let p4 = time splittab
 <<~p .=>. q .<=>. ~q .=>. p>>;;

let p5 = time splittab
 <<(p .|. q .=>. p .|. r) .=>. p .|. (q .=>. r)>>;;

let p6 = time splittab
 <<p .|. ~p>>;;

let p7 = time splittab
 <<p .|. ~ ~ ~p>>;;

let p8 = time splittab
 <<((p .=>. q) .=>. p) .=>. p>>;;

let p9 = time splittab
 <<(p .|. q) .&. (~p .|. q) .&. (p .|. ~q) .=>. ~(~q .|. ~q)>>;;

let p10 = time splittab
 <<(q .=>. r) .&. (r .=>. p .&. q) .&. (p .=>. q .&. r) .=>. (p .<=>. q)>>;;

let p11 = time splittab
 <<p .<=>. p>>;;

let p12 = time splittab
 <<((p .<=>. q) .<=>. r) .<=>. (p .<=>. (q .<=>. r))>>;;

let p13 = time splittab
 <<p .|. q .&. r .<=>. (p .|. q) .&. (p .|. r)>>;;

let p14 = time splittab
 <<(p .<=>. q) .<=>. (q .|. ~p) .&. (~q .|. p)>>;;

let p15 = time splittab
 <<p .=>. q .<=>. ~p .|. q>>;;

let p16 = time splittab
 <<(p .=>. q) .|. (q .=>. p)>>;;

let p17 = time splittab
 <<p .&. (q .=>. r) .=>. s .<=>. (~p .|. q .|. s) .&. (~p .|. ~r .|. s)>>;;

-- -------------------------------------------------------------------------
-- Pelletier problems: monadic predicate logic.
-- -------------------------------------------------------------------------

let p18 = time splittab
 <<exists y. for_all x. P[vt "y"] .=>. P[vt "x"]>>;;

let p19 = time splittab
 <<exists x. for_all y z. (P[vt "y"] .=>. Q[vt "z"]) .=>. P[vt "x"] .=>. Q[vt "x"]>>;;

let p20 = time splittab
 <<(for_all x y. exists z. for_all w. P[vt "x"] .&. Q[vt "y"] .=>. R[vt "z"] .&. U[vt "w"])
   .=>. (exists x y. P[vt "x"] .&. Q[vt "y"]) .=>. (exists z. R[vt "z"])>>;;

let p21 = time splittab
 <<(exists x. P .=>. Q[vt "x"]) .&. (exists x. Q[vt "x"] .=>. P)
   .=>. (exists x. P .<=>. Q[vt "x"])>>;;

let p22 = time splittab
 <<(for_all x. P .<=>. Q[vt "x"]) .=>. (P .<=>. (for_all x. Q[vt "x"]))>>;;

let p23 = time splittab
 <<(for_all x. P .|. Q[vt "x"]) .<=>. P .|. (for_all x. Q[vt "x"])>>;;

let p24 = time splittab
 <<~(exists x. U[vt "x"] .&. Q[vt "x"]) .&.
   (for_all x. P[vt "x"] .=>. Q[vt "x"] .|. R[vt "x"]) .&.
   ~(exists x. P[vt "x"] .=>. (exists x. Q[vt "x"])) .&.
   (for_all x. Q[vt "x"] .&. R[vt "x"] .=>. U[vt "x"]) .=>.
   (exists x. P[vt "x"] .&. R[vt "x"])>>;;

let p25 = time splittab
 <<(exists x. P[vt "x"]) .&.
   (for_all x. U[vt "x"] .=>. ~G[vt "x"] .&. R[vt "x"]) .&.
   (for_all x. P[vt "x"] .=>. G[vt "x"] .&. U[vt "x"]) .&.
   ((for_all x. P[vt "x"] .=>. Q[vt "x"]) .|. (exists x. Q[vt "x"] .&. P[vt "x"]))
   .=>. (exists x. Q[vt "x"] .&. P[vt "x"])>>;;

let p26 = time splittab
 <<((exists x. P[vt "x"]) .<=>. (exists x. Q[vt "x"])) .&.
   (for_all x y. P[vt "x"] .&. Q[vt "y"] .=>. (R[vt "x"] .<=>. U[vt "y"]))
   .=>. ((for_all x. P[vt "x"] .=>. R[vt "x"]) .<=>. (for_all x. Q[vt "x"] .=>. U[vt "x"]))>>;;

let p27 = time splittab
 <<(exists x. P[vt "x"] .&. ~Q[vt "x"]) .&.
   (for_all x. P[vt "x"] .=>. R[vt "x"]) .&.
   (for_all x. U[vt "x"] .&. V[vt "x"] .=>. P[vt "x"]) .&.
   (exists x. R[vt "x"] .&. ~Q[vt "x"])
   .=>. (for_all x. U[vt "x"] .=>. ~R[vt "x"])
       .=>. (for_all x. U[vt "x"] .=>. ~V[vt "x"])>>;;

let p28 = time splittab
 <<(for_all x. P[vt "x"] .=>. (for_all x. Q[vt "x"])) .&.
   ((for_all x. Q[vt "x"] .|. R[vt "x"]) .=>. (exists x. Q[vt "x"] .&. R[vt "x"])) .&.
   ((exists x. R[vt "x"]) .=>. (for_all x. L[vt "x"] .=>. M[vt "x"])) .=>.
   (for_all x. P[vt "x"] .&. L[vt "x"] .=>. M[vt "x"])>>;;

let p29 = time splittab
 <<(exists x. P[vt "x"]) .&. (exists x. G[vt "x"]) .=>.
   ((for_all x. P[vt "x"] .=>. H[vt "x"]) .&. (for_all x. G[vt "x"] .=>. J[vt "x"]) .<=>.
    (for_all x y. P[vt "x"] .&. G[vt "y"] .=>. H[vt "x"] .&. J[vt "y"]))>>;;

let p30 = time splittab
 <<(for_all x. P[vt "x"] .|. G[vt "x"] .=>. ~H[vt "x"]) .&.
   (for_all x. (G[vt "x"] .=>. ~U[vt "x"]) .=>. P[vt "x"] .&. H[vt "x"])
   .=>. (for_all x. U[vt "x"])>>;;

let p31 = time splittab
 <<~(exists x. P[vt "x"] .&. (G[vt "x"] .|. H[vt "x"])) .&.
   (exists x. Q[vt "x"] .&. P[vt "x"]) .&.
   (for_all x. ~H[vt "x"] .=>. J[vt "x"])
   .=>. (exists x. Q[vt "x"] .&. J[vt "x"])>>;;

let p32 = time splittab
 <<(for_all x. P[vt "x"] .&. (G[vt "x"] .|. H[vt "x"]) .=>. Q[vt "x"]) .&.
   (for_all x. Q[vt "x"] .&. H[vt "x"] .=>. J[vt "x"]) .&.
   (for_all x. R[vt "x"] .=>. H[vt "x"])
   .=>. (for_all x. P[vt "x"] .&. R[vt "x"] .=>. J[vt "x"])>>;;

let p33 = time splittab
 <<(for_all x. P[vt "a"] .&. (P[vt "x"] .=>. P[vt "b"]) .=>. P[vt "c"]) .<=>.
   (for_all x. P[vt "a"] .=>. P[vt "x"] .|. P[vt "c"]) .&. (P[vt "a"] .=>. P[vt "b"] .=>. P[vt "c"])>>;;

let p34 = time splittab
 <<((exists x. for_all y. P[vt "x"] .<=>. P[vt "y"]) .<=>.
    ((exists x. Q[vt "x"]) .<=>. (for_all y. Q[vt "y"]))) .<=>.
   ((exists x. for_all y. Q[vt "x"] .<=>. Q[vt "y"]) .<=>.
    ((exists x. P[vt "x"]) .<=>. (for_all y. P[vt "y"])))>>;;

let p35 = time splittab
 <<exists x y. P(x,y) .=>. (for_all x y. P(x,y))>>;;

-- -------------------------------------------------------------------------
-- Full predicate logic (without identity and functions).
-- -------------------------------------------------------------------------

let p36 = time splittab
 <<(for_all x. exists y. P(x,y)) .&.
   (for_all x. exists y. G(x,y)) .&.
   (for_all x y. P(x,y) .|. G(x,y)
   .=>. (for_all z. P(y,z) .|. G(y,z) .=>. H(x,z)))
       .=>. (for_all x. exists y. H(x,y))>>;;

let p37 = time splittab
 <<(for_all z.
     exists w. for_all x. exists y. (P(x,z) .=>. P(y,w)) .&. P(y,z) .&.
     (P(y,w) .=>. (exists u. Q(u,w)))) .&.
   (for_all x z. ~P(x,z) .=>. (exists y. Q(y,z))) .&.
   ((exists x y. Q(x,y)) .=>. (for_all x. R(x,x))) .=>.
   (for_all x. exists y. R(x,y))>>;;

let p38 = time splittab
 <<(for_all x.
     P[vt "a"] .&. (P[vt "x"] .=>. (exists y. P[vt "y"] .&. R(x,y))) .=>.
     (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))) .<=>.
   (for_all x.
     (~P[vt "a"] .|. P[vt "x"] .|. (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))) .&.
     (~P[vt "a"] .|. ~(exists y. P[vt "y"] .&. R(x,y)) .|.
     (exists z w. P[vt "z"] .&. R(x,w) .&. R(w,z))))>>;;

let p39 = time splittab
 <<~(exists x. for_all y. P(y,x) .<=>. ~P(y,y))>>;;

let p40 = time splittab
 <<(exists y. for_all x. P(x,y) .<=>. P(x,x))
  .=>. ~(for_all x. exists y. for_all z. P(z,y) .<=>. ~P(z,x))>>;;

let p41 = time splittab
 <<(for_all z. exists y. for_all x. P(x,y) .<=>. P(x,z) .&. ~P(x,x))
  .=>. ~(exists z. for_all x. P(x,z))>>;;

let p42 = time splittab
 <<~(exists y. for_all x. P(x,y) .<=>. ~(exists z. P(x,z) .&. P(z,x)))>>;;

let p43 = time splittab
 <<(for_all x y. Q(x,y) .<=>. for_all z. P(z,x) .<=>. P(z,y))
   .=>. for_all x y. Q(x,y) .<=>. Q(y,x)>>;;

let p44 = time splittab
 <<(for_all x. P[vt "x"] .=>. (exists y. G[vt "y"] .&. H(x,y)) .&.
   (exists y. G[vt "y"] .&. ~H(x,y))) .&.
   (exists x. J[vt "x"] .&. (for_all y. G[vt "y"] .=>. H(x,y))) .=>.
   (exists x. J[vt "x"] .&. ~P[vt "x"])>>;;

let p45 = time splittab
 <<(for_all x.
     P[vt "x"] .&. (for_all y. G[vt "y"] .&. H(x,y) .=>. J(x,y)) .=>.
       (for_all y. G[vt "y"] .&. H(x,y) .=>. R[vt "y"])) .&.
   ~(exists y. L[vt "y"] .&. R[vt "y"]) .&.
   (exists x. P[vt "x"] .&. (for_all y. H(x,y) .=>.
     L[vt "y"]) .&. (for_all y. G[vt "y"] .&. H(x,y) .=>. J(x,y))) .=>.
   (exists x. P[vt "x"] .&. ~(exists y. G[vt "y"] .&. H(x,y)))>>;;

let p46 = time splittab
 <<(for_all x. P[vt "x"] .&. (for_all y. P[vt "y"] .&. H(y,x) .=>. G[vt "y"]) .=>. G[vt "x"]) .&.
   ((exists x. P[vt "x"] .&. ~G[vt "x"]) .=>.
    (exists x. P[vt "x"] .&. ~G[vt "x"] .&.
               (for_all y. P[vt "y"] .&. ~G[vt "y"] .=>. J(x,y)))) .&.
   (for_all x y. P[vt "x"] .&. P[vt "y"] .&. H(x,y) .=>. ~J(y,x)) .=>.
   (for_all x. P[vt "x"] .=>. G[vt "x"])>>;;

-- -------------------------------------------------------------------------
-- Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.
-- -------------------------------------------------------------------------

let p55 = time splittab
 <<lives(agatha) .&. lives(butler) .&. lives(charles) .&.
   (killed(agatha,agatha) .|. killed(butler,agatha) .|.
    killed(charles,agatha)) .&.
   (for_all x y. killed(x,y) .=>. hates(x,y) .&. ~richer(x,y)) .&.
   (for_all x. hates(agatha,x) .=>. ~hates(charles,x)) .&.
   (hates(agatha,agatha) .&. hates(agatha,charles)) .&.
   (for_all x. lives[vt "x"] .&. ~richer(x,agatha) .=>. hates(butler,x)) .&.
   (for_all x. hates(agatha,x) .=>. hates(butler,x)) .&.
   (for_all x. ~hates(x,agatha) .|. ~hates(x,butler) .|. ~hates(x,charles))
   .=>. killed(agatha,agatha) .&.
       ~killed(butler,agatha) .&.
       ~killed(charles,agatha)>>;;

let p57 = time splittab
 <<P(f([vt "a"],b),f(b,c)) .&.
   P(f(b,c),f(a,c)) .&.
   (for_all [vt "x"] y z. P(x,y) .&. P(y,z) .=>. P(x,z))
   .=>. P(f(a,b),f(a,c))>>;;

-- -------------------------------------------------------------------------
-- See info-hol, circa 1500.
-- -------------------------------------------------------------------------

let p58 = time splittab
 <<for_all P Q R. for_all x. exists v. exists w. for_all y. for_all z.
    ((P[vt "x"] .&. Q[vt "y"]) .=>. ((P[vt "v"] .|. R[vt "w"])  .&. (R[vt "z"] .=>. Q[vt "v"])))>>;;

let p59 = time splittab
 <<(for_all x. P[vt "x"] .<=>. ~P(f[vt "x"])) .=>. (exists x. P[vt "x"] .&. ~P(f[vt "x"]))>>;;

let p60 = time splittab
 <<for_all x. P(x,f[vt "x"]) .<=>.
            exists y. (for_all z. P(z,y) .=>. P(z,f[vt "x"])) .&. P(x,y)>>;;

-- -------------------------------------------------------------------------
-- From Gilmore's classic paper.
-- -------------------------------------------------------------------------

{- **** This is still too hard for us! Amazing...

let gilmore_1 = time splittab
 <<exists x. for_all y z.
      ((F[vt "y"] .=>. G[vt "y"]) .<=>. F[vt "x"]) .&.
      ((F[vt "y"] .=>. H[vt "y"]) .<=>. G[vt "x"]) .&.
      (((F[vt "y"] .=>. G[vt "y"]) .=>. H[vt "y"]) .<=>. H[vt "x"])
      .=>. F[vt "z"] .&. G[vt "z"] .&. H[vt "z"]>>;;

 ***** -}

{- ** This is not valid, according to Gilmore

let gilmore_2 = time splittab
 <<exists x y. for_all z.
        (F(x,z) .<=>. F(z,y)) .&. (F(z,y) .<=>. F(z,z)) .&. (F(x,y) .<=>. F(y,x))
        .=>. (F(x,y) .<=>. F(x,z))>>;;

 ** -}

let gilmore_3 = time splittab
 <<exists x. for_all y z.
        ((F(y,z) .=>. (G[vt "y"] .=>. H[vt "x"])) .=>. F(x,x)) .&.
        ((F(z,x) .=>. G[vt "x"]) .=>. H[vt "z"]) .&.
        F(x,y)
        .=>. F(z,z)>>;;

let gilmore_4 = time splittab
 <<exists x y. for_all z.
        (F(x,y) .=>. F(y,z) .&. F(z,z)) .&.
        (F(x,y) .&. G(x,y) .=>. G(x,z) .&. G(z,z))>>;;

let gilmore_5 = time splittab
 <<(for_all x. exists y. F(x,y) .|. F(y,x)) .&.
   (for_all x y. F(y,x) .=>. F(y,y))
   .=>. exists z. F(z,z)>>;;

let gilmore_6 = time splittab
 <<for_all x. exists y.
        (exists u. for_all v. F(u,x) .=>. G(v,u) .&. G(u,x))
        .=>. (exists u. for_all v. F(u,y) .=>. G(v,u) .&. G(u,y)) .|.
            (for_all u v. exists w. G(v,u) .|. H(w,y,u) .=>. G(u,w))>>;;

let gilmore_7 = time splittab
 <<(for_all x. K[vt "x"] .=>. exists y. L[vt "y"] .&. (F(x,y) .=>. G(x,y))) .&.
   (exists z. K[vt "z"] .&. for_all u. L[vt "u"] .=>. F(z,u))
   .=>. exists v w. K[vt "v"] .&. L[vt "w"] .&. G(v,w)>>;;

let gilmore_8 = time splittab
 <<exists x. for_all y z.
        ((F(y,z) .=>. (G[vt "y"] .=>. (for_all u. exists v. H(u,v,x)))) .=>. F(x,x)) .&.
        ((F(z,x) .=>. G[vt "x"]) .=>. (for_all u. exists v. H(u,v,z))) .&.
        F(x,y)
        .=>. F(z,z)>>;;

let gilmore_9 = time splittab
 <<for_all x. exists y. for_all z.
        ((for_all u. exists v. F(y,u,v) .&. G(y,u) .&. ~H(y,x))
          .=>. (for_all u. exists v. F(x,u,v) .&. G(z,u) .&. ~H(x,z))
          .=>. (for_all u. exists v. F(x,u,v) .&. G(y,u) .&. ~H(x,y))) .&.
        ((for_all u. exists v. F(x,u,v) .&. G(y,u) .&. ~H(x,y))
         .=>. ~(for_all u. exists v. F(x,u,v) .&. G(z,u) .&. ~H(x,z))
         .=>. (for_all u. exists v. F(y,u,v) .&. G(y,u) .&. ~H(y,x)) .&.
             (for_all u. exists v. F(z,u,v) .&. G(y,u) .&. ~H(z,y)))>>;;

-- -------------------------------------------------------------------------
-- Example from Davis-Putnam papers where Gilmore procedure is poor.
-- -------------------------------------------------------------------------

let davis_putnam_example = time splittab
 <<exists x. exists y. for_all z.
        (F(x,y) .=>. (F(y,z) .&. F(z,z))) .&.
        ((F(x,y) .&. G(x,y)) .=>. (G(x,z) .&. G(z,z)))>>;;

************ -}

-}

testTableaux :: Test
testTableaux = TestLabel "Tableaux" (TestList [p20, p19, p38])
