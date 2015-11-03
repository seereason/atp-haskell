{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes, KindSignatures, OverloadedStrings, TypeFamilies #-}
{-# OPTIONS_GHC -fwarn-unused-binds -fwarn-missing-signatures #-}

import Prelude hiding (negate,sum,pred)
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace

import Prelude hiding (negate,sum)
import qualified Data.Set as S
import Data.List (intercalate,minimumBy,maximumBy)
import Data.Maybe
import qualified Data.Map as M

import Lib (distrib, allpairs, flatten, Marked)
import Lit (Literal, unmarkLiteral)
import Formulas (AtomOf, negate, positive, negative, atom_union, (.&.), (.~.), (.=>.))
import Prop (trivial, psimplify1, simpdnf, markPropositional, Propositional, unmarkPropositional)
import FOL (fv, fvt, generalize, subst, IsVariable(variant), IsFunction(variantFunction), V(V), functions)
import Skolem (runSkolem, skolemize)

import ZTypes (Formula(..), FOL(..), Term(..), Function(..))
import ZInstances ()
-- import ZParser (parseFOL)

main = print p45

p45fm :: Formula FOL
--p45fm = parseFOL ("(forall x. P(x) & (forall y. G(y) & H(x,y) ==> J(x,y)) ==> (forall y. G(y) & H(x,y) ==> R(y))) & ~(exists y. L(y) & R(y)) & (exists x. P(x) & (forall y. H(x,y) ==> L(y)) & (forall y. G(y) & H(x,y) ==> J(x,y))) ==> (exists x. P(x) & ~(exists y. G(y) & H(x,y)))" :: String)
p45fm = Imp (And (Forall "x" (Imp (And (Atom (R "P" [Var "x"])) (Forall "y" (Imp (And (Atom (R "G" [Var "y"])) (Atom (R "H" [Var "x",Var "y"]))) (Atom (R "J" [Var "x",Var "y"]))))) (Forall "y" (Imp (And (Atom (R "G" [Var "y"])) (Atom (R "H" [Var "x",Var "y"]))) (Atom (R "R" [Var "y"])))))) (And (Not (Exists "y" (And (Atom (R "L" [Var "y"])) (Atom (R "R" [Var "y"]))))) (Exists "x" (And (Atom (R "P" [Var "x"])) (And (Forall "y" (Imp (Atom (R "H" [Var "x",Var "y"])) (Atom (R "L" [Var "y"])))) (Forall "y" (Imp (And (Atom (R "G" [Var "y"])) (Atom (R "H" [Var "x",Var "y"]))) (Atom (R "J" [Var "x",Var "y"]))))))))) (Exists "x" (And (Atom (R "P" [Var "x"])) (Not (Exists "y" (And (Atom (R "G" [Var "y"])) (Atom (R "H" [Var "x",Var "y"])))))))
p45 :: Int
p45 = gilmore p45fm

fpf :: Ord k => [k] -> [a] -> M.Map k a
fpf xs ys = M.fromList $ zip xs ys

gilmore :: Formula FOL -> Int
gilmore fm = length (gilmore_loop dnf (S.toList cntms) funcs (S.toList fvs) 0 (S.singleton S.empty) [] [])
 where
  dnf :: S.Set (S.Set (Formula FOL))
  dnf = S.map (S.map (unmarkPropositional . unmarkLiteral)) (simpdnf id (markPropositional sfm) :: S.Set (S.Set (Marked Literal (Marked Propositional (Formula FOL)))))
  sfm :: Marked Propositional (Formula FOL)
  sfm = runSkolem (skolemize id (Not (generalize fm)))
  fvs :: S.Set V
  fvs = fv sfm
  cntms = S.map (\(c,_) -> Fn c []) consts
  (consts,funcs) = herbfuns (unmarkPropositional sfm)

gilmore_loop :: (Foldable foldable) =>
                S.Set (S.Set (Formula FOL))
             -> [Term]
             -> foldable (Function, Int)
             -> [V]
             -> Integer
             -> S.Set (S.Set (Formula FOL))
             -> [[Term]]
             -> [[Term]]
             -> [[Term]]
gilmore_loop = herbloop mfn (not . S.null)
    where
      mfn :: S.Set (S.Set (Formula FOL))
          -> (Formula FOL -> Formula FOL)
          -> S.Set (S.Set (Formula FOL))
          -> S.Set (S.Set (Formula FOL))
      mfn djs0 ifn djs = S.filter (not . trivial) (distrib (S.map (S.map ifn) djs0) djs)

herbloop :: forall foldable. (Foldable foldable) =>
            (S.Set (S.Set (Formula FOL)) -> (Formula FOL -> Formula FOL) -> S.Set (S.Set (Formula FOL)) -> S.Set (S.Set (Formula FOL)))
         -> (S.Set (S.Set (Formula FOL)) -> Bool)
         -> S.Set (S.Set (Formula FOL))
         -> [Term]
         -> foldable (Function, Int)
         -> [V]
         -> Integer
         -> S.Set (S.Set (Formula FOL))
         -> [[Term]]
         -> [[Term]]
         -> [[Term]]
herbloop mfn tfn f10 cntms funcs fvs n fl tried tuples = trace ((show (length tried)) ++ " ground instances tried; " ++ (show (length fl)) ++ " items in list")
   (case tuples of
      [] -> let newtups = groundtuples cntms funcs n (length fvs) in
            herbloop mfn tfn f10 cntms funcs fvs (n + 1) fl tried newtups
      (tup : tups) -> let fl' = mfn f10 (subst (fpf fvs tup)) fl in
                      if (not (tfn fl')) then tup : tried else
                      herbloop mfn tfn f10 cntms funcs fvs n fl' (tup : tried) tups)

groundterms :: forall (t :: * -> *) a a1.
                     (Enum a, Eq a, Eq a1, Num a, Num a1, Foldable t) =>
                     [Term] -> t (Function, a1) -> a -> [Term]
groundterms cntms funcs 0 = cntms
groundterms cntms funcs n = foldr (\(f,m) l -> map (\args -> Fn f args) (groundtuples cntms funcs (n-1) m) ++ l) [] funcs

groundtuples :: forall (t :: * -> *) a a1.
                      (Enum a, Eq a, Eq a1, Num a, Num a1, Foldable t) =>
                      [Term] -> t (Function, a1) -> a -> a1 -> [[Term]]
groundtuples cntms funcs 0 0 = [[]]
groundtuples cntms funcs n 0 = []
groundtuples cntms funcs n m = foldr (\k l -> allpairs (\h t -> h : t) (groundterms cntms funcs k) (groundtuples cntms funcs (n - k) (m - 1)) ++ l) [] [0 .. n]

-- Section 3.7

herbfuns :: Formula FOL -> (S.Set (Function, Int), S.Set (Function, Int))
herbfuns fm
  | null cns = (S.singleton ("c",0),fns)
  | otherwise = (cns,fns)
 where
  (cns,fns) = S.partition (\(_,ar) -> ar == 0) (functions fm)
