{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes, KindSignatures, TypeFamilies #-}
{-# OPTIONS_GHC -fwarn-unused-binds -fwarn-missing-signatures #-}
module ZFirstOrderLogic
    ( p45
    ) where

import Prelude hiding (negate,sum,pred)
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace

import Prelude hiding (negate,sum)
import qualified Data.Set as S
import Data.List (intercalate,minimumBy,maximumBy)
import Data.Maybe
import qualified Data.Map as M

import Lib (distrib)
import Formulas (AtomOf, negate, positive, negative, atom_union)
import ZPropositionalLogic (simpdnf, trivial, psimplify1)
import ZTypes (Formula(..), FOL(..), Term(..), itlist, allpairs, unions)
import ZInstances ()
import ZParser (parseFOL)
import ZFailing (Failing, isSuccess, fromSuccess, failure)

{-
p20 :: Formula FOL
p20 = parseFOL "(forall x y. exists z. forall w. P(x) & Q(y) ==> R(z) & U(w)) ==> (exists x y. P(x) & Q(y)) ==> (exists z. R(z))"
-}
p45 :: Int
p45 = gilmore (parseFOL ("(forall x. P(x) & (forall y. G(y) & H(x,y) ==> J(x,y)) ==> (forall y. G(y) & H(x,y) ==> R(y))) & ~(exists y. L(y) & R(y)) & (exists x. P(x) & (forall y. H(x,y) ==> L(y)) & (forall y. G(y) & H(x,y) ==> J(x,y))) ==> (exists x. P(x) & ~(exists y. G(y) & H(x,y)))" :: String) :: Formula FOL)
{-
p24 :: Formula FOL
p24 = parseFOL "~(exists x. U(x) & Q(x)) & (forall x. P(x) ==> Q(x) | R(x)) & ~(exists x. P(x) ==> (exists x. Q(x))) & (forall x. Q(x) & R(x) ==> U(x)) ==> (exists x. P(x) & R(x))"
-}

fpf :: Ord k => [k] -> [a] -> M.Map k a
fpf xs ys = M.fromList $ zip xs ys

#if 0
gilmore :: forall fof pf lit atom term v function.
           (IsFirstOrder fof, Ord fof, HasSkolem function v,
            pf ~ Marked Propositional fof,
            lit ~ Marked Literal pf,
            atom ~ AtomOf lit,
            term ~ TermOf atom,
            v ~ VarOf fof,
            v ~ VarOf pf,
            v ~ VarOf lit,
            v ~ TVarOf term,
            function ~ FunOf term) =>
           fof -> Int
gilmore fm = length (gilmore_loop (simpdnf id sfm :: Set (Set lit)) (Set.toList cntms) funcs (Set.toList fvs) 0 (Set.singleton Set.empty) [] [])
 where
   sfm :: pf
   sfm = runSkolem (skolemize id ((.~.) (generalize fm)))
   fvs = fv sfm
   cntms = Set.map (\(c,_) -> fApp c []) consts
   (consts,funcs) = herbfuns sfm
#else
gilmore :: Formula FOL -> Int
gilmore fm = length (gilmore_loop (simpdnf sfm) (S.toList cntms) funcs (S.toList fvs) 0 (S.singleton S.empty) [] [])
 where
  sfm = skolemize (Not (generalize fm))
  fvs = fv sfm
  cntms = S.map (\(c,_) -> Fn c []) consts
  (consts,funcs) = herbfuns sfm
#endif

gilmore_loop :: (Foldable foldable) =>
                S.Set (S.Set (Formula FOL))
             -> [Term]
             -> foldable (String, Int)
             -> [String]
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
         -> foldable (String, Int)
         -> [String]
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
                     [Term] -> t (String, a1) -> a -> [Term]
groundterms cntms funcs 0 = cntms
groundterms cntms funcs n = itlist (\(f,m) l -> map (\args -> Fn f args) (groundtuples cntms funcs (n-1) m) ++ l) funcs []

groundtuples :: forall (t :: * -> *) a a1.
                      (Enum a, Eq a, Eq a1, Num a, Num a1, Foldable t) =>
                      [Term] -> t (String, a1) -> a -> a1 -> [[Term]]
groundtuples cntms funcs 0 0 = [[]]
groundtuples cntms funcs n 0 = []
groundtuples cntms funcs n m = itlist (\k l -> allpairs (\h t -> h : t) (groundterms cntms funcs k) (groundtuples cntms funcs (n - k) (m - 1)) ++ l) [0 .. n] []

-- Section 3.7

herbfuns :: Formula FOL -> (S.Set (String, Int), S.Set (String, Int))
herbfuns fm
  | null cns = (S.singleton ("c",0),fns)
  | otherwise = (cns,fns)
 where
  (cns,fns) = S.partition (\(_,ar) -> ar == 0) (functions fm)

-- Section 3.6

skolemize :: Formula FOL -> Formula FOL
skolemize fm = specialize (pnf (askolemize fm))

specialize :: Formula t -> Formula t
specialize (Forall _ p) = specialize p
specialize fm = fm

askolemize :: Formula FOL -> Formula FOL
askolemize fm = fst (skolem (nnf (simplify fm)) (S.map fst (functions fm)))

funcs :: Term -> S.Set (String, Int)
funcs (Var _) = S.empty
funcs (Fn f args) = S.insert (f,length args) (S.unions (map funcs args))

functions :: AtomOf (Formula FOL) ~ FOL => Formula FOL -> S.Set (String, Int)
functions fm = atom_union (\(R _ a) -> S.unions (map funcs a)) fm

skolem :: Formula FOL -> S.Set String -> (Formula FOL, S.Set String)
skolem fm@(Exists y p) fns = skolem (subst (M.singleton y fx) p) (S.insert f fns)
 where
  xs = fv fm
  f = variant (if S.null xs then "c_"++y else "f_"++y) fns
  fx = Fn f (map Var (S.toList xs))
skolem fm@(Forall x p) fns = (Forall x p',fns')
 where
  (p',fns') = skolem p fns
skolem fm@(And p q) fns = skolem2 (uncurry And) (p,q) fns
skolem fm@(Or p q) fns = skolem2 (uncurry Or) (p,q) fns
skolem fm fns = (fm,fns)

skolem2 :: forall t.
                 ((Formula FOL, Formula FOL) -> t)
                 -> (Formula FOL, Formula FOL) -> S.Set String -> (t, S.Set String)
skolem2 cons (p,q) fns = (cons (p',q'),fns'')
 where
  (p',fns') = skolem p fns
  (q',fns'') = skolem q fns'

-- Section 3.5

pnf :: Formula FOL -> Formula FOL
pnf fm = prenex (nnf (simplify fm))

prenex :: Formula FOL -> Formula FOL
prenex (Forall x p) = Forall x (prenex p)
prenex (Exists x p) = Exists x (prenex p)
prenex (And p q) = pullquants (And (prenex p) (prenex q))
prenex (Or p q) = pullquants (Or (prenex p) (prenex q))
prenex fm = fm

pullquants :: Formula FOL -> Formula FOL
pullquants fm@(And (Forall x p) (Forall y q)) = pullq (True,True) fm Forall And x y p q
pullquants fm@(Or (Exists x p) (Exists y q)) = pullq (True,True) fm Exists Or x y p q
pullquants fm@(And (Forall x p) q) = pullq (True,False) fm Forall And x x p q
pullquants fm@(And p (Forall y q)) = pullq (False,True) fm Forall And y y p q
pullquants fm@(Or (Forall x p) q) = pullq (True,False) fm Forall Or x x p q
pullquants fm@(Or p (Forall y q)) = pullq (False,True) fm Forall Or y y p q
pullquants fm@(And (Exists x p) q) = pullq (True,False) fm Exists And x x p q
pullquants fm@(And p (Exists y q)) = pullq (False,True) fm Exists And y y p q
pullquants fm@(Or (Exists x p) q) = pullq (True,False) fm Exists Or x x p q
pullquants fm@(Or p (Exists y q)) = pullq (False,True) fm Exists Or y y p q
pullquants fm = fm

pullq :: (Bool, Bool)
               -> Formula FOL
               -> (String -> Formula FOL -> t)
               -> (Formula FOL -> Formula FOL -> Formula FOL)
               -> String
               -> String
               -> Formula FOL
               -> Formula FOL
               -> t
pullq (l,r) fm quant op x y p q = quant z (pullquants (op p' q'))
 where
  z = variant x (fv fm)
  p' = if l then subst (M.singleton x (Var z)) p else p
  q' = if r then subst (M.singleton y (Var z)) q else q

nnf :: Formula a -> Formula a
nnf (And p q) = And (nnf p) (nnf q)
nnf (Or p q) = Or (nnf p) (nnf q)
nnf (Imp p q) = Or (nnf (Not p)) (nnf q)
nnf (Iff p q) = Or (And (nnf p) (nnf q)) (And (nnf (Not p)) (nnf (Not q)))
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = Or (nnf (Not p)) (nnf (Not q))
nnf (Not (Or p q)) = And (nnf (Not p)) (nnf (Not q))
nnf (Not (Imp p q)) = And (nnf p) (nnf (Not q))
nnf (Not (Iff p q)) = Or (And (nnf p) (nnf (Not q))) (And (nnf (Not p)) (nnf q))
nnf (Forall x p) = Forall x (nnf p)
nnf (Exists x p) = Exists x (nnf p)
nnf (Not (Forall x p)) = Exists x (nnf (Not p))
nnf (Not (Exists x p)) = Forall x (nnf (Not p))
nnf fm = fm

simplify :: Formula FOL -> Formula FOL
simplify (Not p) = simplify1 (Not (simplify p))
simplify (And p q) = simplify1 (And (simplify p) (simplify q))
simplify (Or p q) = simplify1 (Or (simplify p) (simplify q))
simplify (Imp p q) = simplify1 (Imp (simplify p) (simplify q))
simplify (Iff p q) = simplify1 (Iff (simplify p) (simplify q))
simplify (Forall x p) = simplify1 (Forall x (simplify p))
simplify (Exists x p) = simplify1 (Exists x (simplify p))
simplify fm = fm

simplify1 :: Formula FOL -> Formula FOL
simplify1 fm@(Forall x p)
 | S.member x (fv p) = fm
 | otherwise = p
simplify1 fm@(Exists x p)
 | S.member x (fv p) = fm
 | otherwise = p
simplify1 fm = psimplify1 fm

-- Section 3.4

subst :: M.Map String Term -> Formula FOL -> Formula FOL
subst subfn FF = FF
subst subfn TT = TT
subst subfn (Atom (R p args)) = Atom (R p (map (tsubst subfn) args))
subst subfn (Not p) = Not (subst subfn p)
subst subfn (And p q) = And (subst subfn p) (subst subfn q)
subst subfn (Or p q) = Or (subst subfn p) (subst subfn q)
subst subfn (Imp p q) = Imp (subst subfn p) (subst subfn q)
subst subfn (Iff p q) = Iff (subst subfn p) (subst subfn q)
subst subfn (Forall x p) = substq subfn Forall x p
subst subfn (Exists x p) = substq subfn Exists x p

substq :: M.Map String Term -> (String -> Formula FOL -> t) -> String -> Formula FOL -> t
substq subfn quant x p = quant x' (subst (M.insert x (Var x') subfn) p)
 where x' = if (any (\y -> S.member x (fvt (maybe (Var y) id (M.lookup y subfn))))
                    (S.delete x (fv p)))
            then variant x (fv (subst (M.delete x subfn) p)) else x

variant :: String -> S.Set String -> String
variant x vars
 | S.member x vars = variant (x ++ "'") vars
 | otherwise = x

tsubst :: M.Map String Term -> Term -> Term
tsubst sfn tm@(Var x) = maybe tm id (M.lookup x sfn)
tsubst sfn (Fn f args) = Fn f (map (tsubst sfn) args)

generalize :: Formula FOL -> Formula FOL
generalize fm = itlist Forall (fv fm) fm

-- Section 3.3

fv :: Formula FOL -> S.Set String
fv FF = S.empty
fv TT = S.empty
fv (Atom (R _p args)) = S.unions (map fvt args)
fv (Not p) = fv p
fv (And p q) = S.union (fv p) (fv q)
fv (Or p q) = S.union (fv p) (fv q)
fv (Imp p q) = S.union (fv p) (fv q)
fv (Iff p q) = S.union (fv p) (fv q)
fv (Forall x p) = S.delete x (fv p)
fv (Exists x p) = S.delete x (fv p)

fvt :: Term -> S.Set String
fvt (Var x) = S.singleton x
fvt (Fn _ args) = S.unions (map fvt args)
