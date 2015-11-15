-- | Relation between FOL and propositonal logic; Herbrand theorem.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Logic.ATP.Herbrand where

import Data.Logic.ATP.Apply (functions, HasApply(TermOf))
import Data.Logic.ATP.DP (dpll)
import Data.Logic.ATP.FOL (IsFirstOrder, lsubst, fv, generalize)
import Data.Logic.ATP.Formulas (IsFormula(AtomOf), overatoms, atomic)
import Data.Logic.ATP.Lib (allpairs, distrib)
import Data.Logic.ATP.Lit ((.~.), JustLiteral, LFormula)
import Data.Logic.ATP.Parser(fof)
import Data.Logic.ATP.Pretty (prettyShow)
import Data.Logic.ATP.Prop (eval, JustPropositional, PFormula, simpcnf, simpdnf, trivial)
import Data.Logic.ATP.Skolem (Formula, HasSkolem(SVarOf), runSkolem, skolemize)
import Data.Logic.ATP.Term (Arity, IsTerm(TVarOf, FunOf), fApp)
import qualified Data.Map.Strict as Map
import Data.Set as Set
import Data.String (IsString(..))
import Debug.Trace
import Test.HUnit hiding (tried)

-- | Propositional valuation.
pholds :: (JustPropositional pf) => (AtomOf pf -> Bool) -> pf -> Bool
pholds d fm = eval fm d

-- | Get the constants for Herbrand base, adding nullary one if necessary.
herbfuns :: (atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, IsFormula fof, HasApply atom, Ord function) => fof -> (Set (function, Arity), Set (function, Arity))
herbfuns fm =
  let (cns,fns) = Set.partition (\ (_,ar) -> ar == 0) (functions fm) in
  if Set.null cns then (Set.singleton (fromString "c",0),fns) else (cns,fns)

-- | Enumeration of ground terms and m-tuples, ordered by total fns.
groundterms :: (v ~ TVarOf term, f ~ FunOf term, IsTerm term) => Set term -> Set (f, Arity) -> Int -> Set term
groundterms cntms _ 0 = cntms
groundterms cntms fns n =
    Set.fold terms Set.empty fns
    where
      terms (f,m) l = Set.union (Set.map (fApp f) (groundtuples cntms fns (n - 1) m)) l

groundtuples :: (v ~ TVarOf term, f ~ FunOf term, IsTerm term) => Set term -> Set (f, Int) -> Int -> Int -> Set [term]
groundtuples _ _ 0 0 = Set.singleton []
groundtuples _ _ _ 0 = Set.empty
groundtuples cntms fns n m =
    Set.fold tuples Set.empty (Set.fromList [0 .. n])
    where
      tuples k l = Set.union (allpairs (:) (groundterms cntms fns k) (groundtuples cntms fns (n - k) (m - 1))) l

-- | Iterate modifier "mfn" over ground terms till "tfn" fails.
herbloop :: forall lit atom function v term.
            (atom ~ AtomOf lit, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function,
             JustLiteral lit,
             HasApply atom,
             IsTerm term) =>
            (Set (Set lit) -> (lit -> lit) -> Set (Set lit) -> Set (Set lit))
         -> (Set (Set lit) -> Bool)
         -> Set (Set lit)
         -> Set term
         -> Set (function, Int)
         -> [TVarOf term]
         -> Int
         -> Set (Set lit)
         -> Set [term]
         -> Set [term]
         -> Set [term]
herbloop mfn tfn fl0 cntms fns fvs n fl tried tuples =
  let debug x = trace (show (size tried) ++ " ground instances tried; " ++ show (length fl) ++ " items in list") x in
  case Set.minView (debug tuples) of
    Nothing ->
          let newtups = groundtuples cntms fns n (length fvs) in
          herbloop mfn tfn fl0 cntms fns fvs (n + 1) fl tried newtups
    Just (tup, tups) ->
        let fpf' = Map.fromList (zip fvs tup) in
        let fl' = mfn fl0 (lsubst fpf') fl in
        if not (tfn fl') then Set.insert tup tried
        else herbloop mfn tfn fl0 cntms fns fvs n fl' (Set.insert tup tried) tups

-- | Hence a simple Gilmore-type procedure.
gilmore_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function,
                 JustLiteral lit, Ord lit,
                 HasApply atom,
                 IsTerm term) =>
                Set (Set lit)
             -> Set term
             -> Set (function, Int)
             -> [TVarOf term]
             -> Int
             -> Set (Set lit)
             -> Set [term]
             -> Set [term]
             -> Set [term]
gilmore_loop =
    herbloop mfn (not . Set.null)
    where
      mfn djs0 ifn djs = Set.filter (not . trivial) (distrib (Set.map (Set.map ifn) djs0) djs)

gilmore :: forall fof atom term v function.
           (IsFirstOrder fof, Ord fof, HasSkolem function,
            atom ~ AtomOf fof,
            term ~ TermOf atom,
            function ~ FunOf term,
            v ~ TVarOf term,
            v ~ SVarOf function) =>
           fof -> Int
gilmore fm =
  let (sfm :: PFormula atom) = runSkolem (skolemize id ((.~.) (generalize fm))) in
  let fvs = Set.toList (overatoms (\ a s -> Set.union s (fv (atomic a :: fof))) sfm (Set.empty))
      (consts,fns) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  Set.size (gilmore_loop (simpdnf id sfm :: Set (Set (LFormula atom))) cntms fns (fvs) 0 (Set.singleton Set.empty) Set.empty Set.empty)

-- | First example and a little tracing.
test01 :: Test
test01 =
    let fm = [fof| exists x. (forall y. p(x) ==> p(y)) |]
        expected = 2
    in
    TestCase (assertString (case gilmore fm of
                              r | r == expected -> ""
                              r -> "gilmore(" ++ prettyShow fm ++ ") -> " ++ show r ++ ", expected: " ++ show expected))

-- -------------------------------------------------------------------------
-- Quick example.
-- -------------------------------------------------------------------------

p24 :: Test
p24 =
     let label = "gilmore p24 (p. 160): " ++ prettyShow fm
         fm = [fof|~(exists x. (U(x) & Q(x))) &
                    (forall x. (P(x) ==> Q(x) | R(x))) &
                   ~(exists x. (P(x) ==> (exists x. Q(x)))) &
                    (forall x. (Q(x) & R(x) ==> U(x)))
                       ==> (exists x. (P(x) & R(x)))|] in
    TestLabel label $ TestCase $ assertEqual label 1 (gilmore fm)

-- | Slightly less easy example.  Expected output:
-- 
-- 0 ground instances tried; 1 items in list
-- 0 ground instances tried; 1 items in list
-- 1 ground instances tried; 13 items in list
-- 1 ground instances tried; 13 items in list
-- 2 ground instances tried; 57 items in list
-- 3 ground instances tried; 84 items in list
-- 4 ground instances tried; 405 items in list
p45fm :: Formula
p45fm =      [fof| (((forall x.
                      ((P(x) & (forall y. ((G(y) & H(x,y)) ==> J(x,y)))) ==>
                       (forall y. ((G(y) & H(x,y)) ==> R(y))))) &
                     ((~(exists y. (L(y) & R(y)))) &
                      (exists x.
                       (P(x) &
                        ((forall y. (H(x,y) ==> L(y))) &
                         (forall y. ((G(y) & H(x,y)) ==> J(x,y)))))))) ==>
                    (exists x. (P(x) & (~(exists y. (G(y) & H(x,y))))))) |]
p45 :: Test
p45 = TestLabel "gilmore p45" $ TestCase $ assertEqual "gilmore p45" 5 (gilmore p45fm)
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

-- | The Davis-Putnam procedure for first order logic.
dp_mfn :: Ord b => Set (Set a) -> (a -> b) -> Set (Set b) -> Set (Set b)
dp_mfn cjs0 ifn cjs = Set.union (Set.map (Set.map ifn) cjs0) cjs

dp_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function,
            JustLiteral lit, Ord lit,
            HasApply atom,
            IsTerm term) =>
           Set (Set lit)
        -> Set term
        -> Set (function, Int)
        -> [v]
        -> Int
        -> Set (Set lit)
        -> Set [term]
        -> Set [term]
        -> Set [term]
dp_loop = herbloop dp_mfn dpll

davisputnam :: forall formula atom term v function.
               (IsFirstOrder formula, Ord formula, HasSkolem function,
                atom ~ AtomOf formula,
                term ~ TermOf atom,
                function ~ FunOf term,
                v ~ TVarOf term,
                v ~ SVarOf function) =>
               formula -> Int
davisputnam fm =
  let (sfm :: PFormula atom) = runSkolem (skolemize id ((.~.)(generalize fm))) in
  let fvs = Set.toList (overatoms (\ a s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
      (consts,fns) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  Set.size (dp_loop (simpcnf id sfm :: Set (Set (LFormula atom))) cntms fns fvs 0 Set.empty Set.empty Set.empty)

{-
-- | Show how much better than the Gilmore procedure this can be.
START_INTERACTIVE;;
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;
-}

-- | Show how few of the instances we really need. Hence unification!
davisputnam' :: forall formula atom term v function.
                (IsFirstOrder formula, Ord formula, HasSkolem function,
                 atom ~ AtomOf formula,
                 term ~ TermOf atom,
                 function ~ FunOf term,
                 v ~ TVarOf term,
                 v ~ SVarOf function) =>
                formula -> formula -> formula -> Int
davisputnam' _ _ fm =
    let (sfm :: PFormula atom) = runSkolem (skolemize id ((.~.)(generalize fm))) in
    let fvs = Set.toList (overatoms (\ (a :: AtomOf formula) s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
        consts :: Set (function, Arity)
        fns :: Set (function, Arity)
        (consts,fns) = herbfuns sfm in
    let cntms :: Set (TermOf (AtomOf formula))
        cntms = Set.map (\ (c,_) -> fApp c []) consts in
    Set.size (dp_refine_loop (simpcnf id sfm :: Set (Set (LFormula atom))) cntms fns fvs 0 Set.empty Set.empty Set.empty)

-- | Try to cut out useless instantiations in final result.
dp_refine_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term, v ~ SVarOf function,
                   JustLiteral lit, Ord lit,
                   IsTerm term,
                   HasApply atom) =>
                  Set (Set lit)
               -> Set term
               -> Set (function, Int)
               -> [v]
               -> Int
               -> Set (Set lit)
               -> Set [term]
               -> Set [term]
               -> Set [term]
dp_refine_loop cjs0 cntms fns fvs n cjs tried tuples =
    let tups = dp_loop cjs0 cntms fns fvs n cjs tried tuples in
    dp_refine cjs0 fvs tups Set.empty

dp_refine :: (atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term,
              HasApply atom,
              JustLiteral lit, Ord lit,
              IsTerm term
             ) => Set (Set lit) -> [TVarOf term] -> Set [term] -> Set [term] -> Set [term]
dp_refine cjs0 fvs dknow need =
    case Set.minView dknow of
      Nothing -> need
      Just (cl, dknow') ->
          let mfn = dp_mfn cjs0 . lsubst . Map.fromList . zip fvs in
          let flag = dpll (Set.fold mfn Set.empty (Set.union need dknow')) in
          dp_refine cjs0 fvs dknow' (if flag then Set.insert cl need else need)

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

testHerbrand :: Test
testHerbrand = TestLabel "Herbrand" (TestList [test01, p24, p45])
