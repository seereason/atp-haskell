-- | Relation between FOL and propositonal logic; Herbrand theorem.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, GADTs, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Herbrand where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import Data.Set as Set
import Data.String (IsString(..))
import Debug.Trace
import Lib (allpairs, distrib)
import DP (dpll)
import FOL (IsFirstOrder, IsTerm, fApp, subst, fv, generalize, exists, for_all, pApp, vt)
import Formulas ((.~.), overatoms, atomic, (.=>.), (.&.), (.|.))
import Lit (IsLiteral)
import Pretty (prettyShow)
import Prop (IsPropositional, eval, trivial, simpcnf, simpdnf)
import Skolem (Arity, functions, HasSkolem, runSkolem, skolemize)
#ifndef NOTESTS
import FOL (V)
import Skolem (MyFormula, MyTerm)
import Test.HUnit hiding (tried)
#endif

-- | Propositional valuation.
pholds :: IsPropositional formula atom => (atom -> Bool) -> formula -> Bool
pholds d fm = eval fm d

-- | Get the constants for Herbrand base, adding nullary one if necessary.
herbfuns :: IsFirstOrder fof atom predicate term v function =>
            fof -> (Set (function, Arity), Set (function, Arity))
herbfuns fm =
  let (cns,fns) = Set.partition (\ (_,ar) -> ar == 0) (functions fm) in
  if Set.null cns then (Set.singleton (fromString "c",0),fns) else (cns,fns)

-- | Enumeration of ground terms and m-tuples, ordered by total fns.
groundterms :: IsTerm term v f => Set term -> Set (f, Arity) -> Int -> Set term
groundterms cntms _ 0 = cntms
groundterms cntms funcs n =
    Set.fold terms Set.empty funcs
    where
      terms (f,m) l = Set.union (Set.map (fApp f) (groundtuples cntms funcs (n - 1) m)) l

groundtuples :: IsTerm term v f => Set term -> Set (f, Int) -> Int -> Int -> Set [term]
groundtuples _ _ 0 0 = Set.singleton []
groundtuples _ _ _ 0 = Set.empty
groundtuples cntms funcs n m =
    Set.fold tuples Set.empty (Set.fromList [0 .. n])
    where
      tuples k l = Set.union (allpairs (:) (groundterms cntms funcs k) (groundtuples cntms funcs (n - k) (m - 1))) l

-- | Iterate modifier "mfn" over ground terms till "tfn" fails.
herbloop :: IsFirstOrder formula atom predicate term v function =>
            (Set (Set lit) -> (formula -> formula) -> Set (Set lit) -> Set (Set lit))
         -> (Set (Set lit) -> Failing Bool)
         -> Set (Set lit)
         -> Set term
         -> Set (function, Int)
         -> [v]
         -> Int
         -> Set (Set lit)
         -> Set [term]
         -> Set [term]
         -> Failing (Set [term])
herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples =
  let debug x = trace (show (size tried) ++ " ground instances tried; " ++ show (length fl) ++ " items in list") x in
  case Set.minView (debug tuples) of
    Nothing ->
          let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtups
    Just (tup, tups) ->
        let fpf' = Map.fromList (zip fvs tup) in
        let fl' = mfn fl0 (subst fpf') fl in
        case tfn fl' of
          Failure msgs -> Failure msgs
          Success x ->
              if not x
              then Success (Set.insert tup tried)
              else herbloop mfn tfn fl0 cntms funcs fvs n fl' (Set.insert tup tried) tups
{-
subst' :: (IsFormula lit atom, IsTerm term v function) => {-forall lit atom term v f. (IsLiteral lit atom, Atom atom term v, Term term v f) =>-} Map.Map v term -> lit -> lit
subst' env fm =
     mapAtoms (atomic . substitute') fm
    where substitute' :: atom -> atom
          substitute' = subst env
-}

-- | Hence a simple Gilmore-type procedure.
gilmore_loop :: (IsFirstOrder lit atom predicate term v function, IsLiteral lit atom) =>
                Set (Set lit)
             -> Set term
             -> Set (function, Int)
             -> [v]
             -> Int
             -> Set (Set lit)
             -> Set [term]
             -> Set [term]
             -> Failing (Set [term])
gilmore_loop =
    herbloop mfn (Success . not . Set.null)
    where
      mfn djs0 ifn djs = Set.filter (not . trivial) (distrib (Set.map (Set.map ifn) djs0) djs)

gilmore :: forall formula atom predicate term function v.
           (IsFirstOrder formula atom predicate term v function,
            IsPropositional formula atom,
            IsLiteral formula atom,
            HasSkolem function v) =>
           formula -> Failing Int
gilmore fm =
  let (sfm :: formula) = runSkolem (skolemize id ((.~.) (generalize fm))) in
  let fvs = Set.toList (overatoms (\ a s -> Set.union s (fv (atomic a :: formula))) sfm (Set.empty))
      (consts,funcs) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  gilmore_loop (simpdnf id sfm :: Set (Set formula)) cntms funcs (fvs) 0 (Set.singleton Set.empty) Set.empty Set.empty >>= return . Set.size

#ifndef NOINSTS
-- | First example and a little tracing.
test01 :: Test
test01 =
    let fm = exists "x" (for_all "y" (pApp "p" [vt "x"] .=>. pApp "p" [vt "y"])) :: MyFormula
        expected = Success 2
    in
    TestCase (assertString (case gilmore fm of
                              r | r == expected -> ""
                              r -> "gilmore(" ++ prettyShow fm ++ ") -> " ++ show r ++ ", expected: " ++ show expected))

-- ------------------------------------------------------------------------- 
-- Quick example.                                                            
-- ------------------------------------------------------------------------- 

test02 :: Test
test02 =
    let x = vt "x"
        p = pApp "P" :: [MyTerm] -> MyFormula
        q = pApp "Q" :: [MyTerm] -> MyFormula
        r = pApp "R" :: [MyTerm] -> MyFormula
        u = pApp "U" :: [MyTerm] -> MyFormula
        fm :: MyFormula
        fm = exists "x" (u[x] .&. q[x] .&. (for_all "x" (p[x] .=>. q[x] .|. r[x])) .&.
                              ((.~.)(exists ("x" :: V) (p[x] .=>. (exists "x" (q[x]))))) .&.
                              (for_all "x" (q[x] .&. r[x] .=>. u[x]))
                              .=>. (exists "x" (p[x] .&. r[x]))) in
    TestCase $ assertEqual ("gilmore p24 (p. 160): " ++ prettyShow fm) (Success 1) (gilmore fm)
{-
let p24 = gilmore
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;
-}
{-
-- ------------------------------------------------------------------------- 
-- Slightly less easy example.                                               
-- ------------------------------------------------------------------------- 

let p45 = gilmore
 <<(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))
              ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\
                      (forall y. G(y) /\ H(x,y) ==> J(x,y)))
   ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
END_INTERACTIVE;;
-}
-- ------------------------------------------------------------------------- 
-- Apparently intractable example.                                           
-- ------------------------------------------------------------------------- 

{-

let p20 = gilmore
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

-}
#endif


-- | The Davis-Putnam procedure for first order logic.
dp_mfn :: Ord b => Set (Set a) -> (a -> b) -> Set (Set b) -> Set (Set b)
dp_mfn cjs0 ifn cjs = Set.union (Set.map (Set.map ifn) cjs0) cjs

dp_loop :: (IsFirstOrder lit atom predicate term v function, IsLiteral lit atom) =>
           Set (Set lit)
        -> Set term
        -> Set (function, Int)
        -> [v]
        -> Int
        -> Set (Set lit)
        -> Set [term]
        -> Set [term]
        -> Failing (Set [term])
dp_loop = herbloop dp_mfn dpll

davisputnam :: forall formula atom term v predicate function.
               (IsLiteral formula atom,
                IsFirstOrder formula atom predicate term v function,
                IsString function,
                HasSkolem function v,
                Ord function) =>
               formula -> Failing Int
davisputnam fm =
  let (sfm :: formula) = runSkolem (skolemize id ((.~.)(generalize fm))) in
  let fvs = Set.toList (overatoms (\ a s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
      (consts,funcs) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  dp_loop (simpcnf id sfm :: Set (Set formula)) cntms funcs fvs 0 Set.empty Set.empty Set.empty >>= return . Set.size

{-
-- | Show how much better than the Gilmore procedure this can be.
START_INTERACTIVE;;
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;
-}

-- | Show how few of the instances we really need. Hence unification!
davisputnam' :: forall formula atom predicate term v f.
                (IsFirstOrder formula atom predicate term v f,
                 IsLiteral formula atom,
                 IsPropositional formula atom,
                 HasSkolem f v,
                 Ord f) =>
                formula -> formula -> formula -> Failing Int
davisputnam' _ _ fm =
    let (sfm :: formula) = runSkolem (skolemize id ((.~.)(generalize fm))) in
    let fvs = Set.toList (overatoms (\ (a :: atom) s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
        (consts,funcs) = herbfuns sfm in
    let cntms = Set.map (\ (c,_) -> fApp c []) consts in
    dp_refine_loop (simpcnf id sfm :: Set (Set formula)) cntms funcs fvs 0 Set.empty Set.empty Set.empty >>= return . Set.size

-- | Try to cut out useless instantiations in final result.
dp_refine_loop :: (IsFirstOrder formula atom predicate term v function, IsLiteral formula atom) =>
                  Set (Set formula)
               -> Set term
               -> Set (function, Int)
               -> [v]
               -> Int
               -> Set (Set formula)
               -> Set [term]
               -> Set [term]
               -> Failing (Set [term])
dp_refine_loop cjs0 cntms funcs fvs n cjs tried tuples =
    dp_loop cjs0 cntms funcs fvs n cjs tried tuples >>= \ tups ->
    dp_refine cjs0 fvs tups Set.empty

dp_refine :: (IsFirstOrder formula atom predicate term v function, IsLiteral formula atom) =>
             Set (Set formula) -> [v] -> Set [term] -> Set [term] -> Failing (Set [term])
dp_refine cjs0 fvs dknow need =
    case Set.minView dknow of
      Nothing -> Success need
      Just (cl, dknow') ->
          let mfn = dp_mfn cjs0 . subst . Map.fromList . zip fvs in
          dpll (Set.fold mfn Set.empty (Set.union need dknow')) >>= \ flag ->
          if flag then return (Set.insert cl need) else return need >>=
          dp_refine cjs0 fvs dknow'

{-
START_INTERACTIVE;;
let p36 = davisputnam'
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
                ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
   ==> (forall x. exists y. H(x,y))>>;;

let p29 = davisputnam'
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;
END_INTERACTIVE;;
-}

#ifndef NOINSTS
tests :: Test
tests = TestList [test01, test02]
#endif
