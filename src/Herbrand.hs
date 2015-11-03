-- | Relation between FOL and propositonal logic; Herbrand theorem.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Herbrand where

import Control.Applicative.Error (Failing(..))
import Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Monoid ((<>))
import Data.Sequence as Seq (Seq)
import Data.Set as Set
import Data.String (IsString(..))
import Debug.Trace

import DP (dpll)
import FOL (Arity, functions, HasApply(TermOf, PredOf), HasApply, IsFirstOrder, IsQuantified(VarOf), IsTerm(TVarOf, FunOf),
            fApp, lsubst, subst, tsubst, asubst, fv, generalize)
import Formulas ((.~.), IsFormula(AtomOf), IsNegatable(foldNegation), overatoms, atomic, positive, negate)
import Lib (allpairs, distrib, failing, fpf, Marked, SetLike(slMap, slView, slUnion, slEmpty, slSingleton), slInsert, prettyFoldable)
import Lit (JustLiteral, Literal, unmarkLiteral)
import Prop (eval, IsPropositional, JustPropositional, Propositional, simpcnf, simpdnf, trivial)
import Skolem (HasSkolem, runSkolem, skolemize)

#ifndef NOTESTS
import FOL (exists, for_all, pApp, V, vt)
import Formulas ((.=>.), (.&.), (.|.))
import Parser(fof)
import Pretty (prettyShow)
import Skolem (MyFormula, MyTerm, Function)
import Test.HUnit hiding (tried)
#endif

-- | Propositional valuation.
pholds :: (IsPropositional pf, JustPropositional pf) => (AtomOf pf -> Bool) -> pf -> Bool
pholds d fm = eval fm d

-- | Get the constants for Herbrand base, adding nullary one if necessary.
herbfuns :: (atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term, IsFormula fof, HasApply atom, Ord function) => fof -> (Set (function, Arity), Set (function, Arity))
herbfuns fm =
  let (cns,fns) = Set.partition (\ (_,ar) -> ar == 0) (functions fm) in
  if Set.null cns then (Set.singleton (fromString "c",0),fns) else (cns,fns)

groundterms :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term, SetLike set) =>
               set term -> Set (f, Arity) -> Int -> set term
groundterms cntms _ 0 = cntms
groundterms cntms funcs n =
    Foldable.foldr (\(f,m) l -> slUnion (slMap (fApp f) (groundtuples cntms funcs (n-1) m)) l) slEmpty funcs

groundtuples :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term, SetLike set) =>
                set term -> Set (f, Int) -> Int -> Int -> set [term]
groundtuples cntms funcs 0 0 = slSingleton mempty
groundtuples cntms funcs n 0 = slEmpty
groundtuples cntms funcs n m =
    Foldable.foldr (\k l -> slUnion (allpairs (:) (groundterms cntms funcs k) (groundtuples cntms funcs (n - k) (m - 1))) l)
                   slEmpty
                   (Set.fromList [0 .. n])

herbloop :: (JustLiteral lit, HasApply atom, IsTerm term, SetLike set,
             atom ~ AtomOf lit, v ~ VarOf lit, v ~ TVarOf term, term ~ TermOf atom, function ~ FunOf term) =>
            (Set (Set lit) -> (lit -> lit) -> Set (Set lit) -> Set (Set lit))
         -> (Set (Set lit) -> Bool)
         -> Set (Set lit)
         -> set term
         -> Set (function, Arity)
         -> [VarOf lit]
         -> Int
         -> Set (Set lit)
         -> set [term]
         -> set [term]
         -> set [term]
herbloop mfn tfn f10 cntms funcs fvs n fl tried tuples =
    case slView (debug (trace ("tuples: " ++ show (prettyFoldable tuples)) tuples)) of
      Nothing ->
          let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn f10 cntms funcs fvs (n + 1) fl tried newtups
      Just (tup, tups) ->
          let fl' = mfn f10 (lsubst (Map.fromList (zip fvs tup))) fl in
          case tfn fl' of
            False -> slInsert tup tried
            True -> herbloop mfn tfn f10 cntms funcs fvs n fl' (slInsert tup tried) tups
    where
      debug x = trace ((show (foldableSize tried)) ++ " ground instances tried; " ++ (show (length fl)) ++ " items in list") x

foldableSize :: Foldable t => t a -> Int
foldableSize = Foldable.foldr (\_ n -> n + 1) 0

gilmore_loop :: forall lit atom term v function set.
                (JustLiteral lit, Ord lit, HasApply atom, IsTerm term, SetLike set, set ~ Seq,
                 atom ~ AtomOf lit, term ~ TermOf atom, v ~ VarOf lit, v ~ TVarOf term, function ~ FunOf term) =>
                Set (Set lit)
             -> set term
             -> Set (function, Arity)
             -> [v]
             -> Int
             -> Set (Set lit)
             -> set [term]
             -> set [term]
             -> set [term]
gilmore_loop = herbloop mfn (not . Prelude.null)
 where mfn :: Set (Set lit) -> (lit -> lit) -> Set (Set lit) -> Set (Set lit)
       mfn djs0 ifn djs = Set.filter (not . trivial) (distrib (Set.map (Set.map ifn) djs0) djs)

gilmore :: forall fof pf lit atom term v function.
           (IsFirstOrder fof, Ord fof, HasSkolem function v,
            pf ~ Marked Propositional fof,
            lit ~ Marked Literal pf,
            atom ~ AtomOf fof, term ~ TermOf atom,
            v ~ VarOf fof,
            v ~ VarOf pf,
            v ~ VarOf lit,
            v ~ TVarOf term,
            function ~ FunOf term) =>
           fof -> Int
gilmore fm = foldableSize $ gilmore_loop (simpdnf id sfm :: Set (Set lit)) cntms funcs (Set.toList fvs) 0 (singleton mempty) mempty mempty
 where
  sfm :: pf
  sfm = runSkolem (skolemize id ((.~.) (generalize fm)))
  fvs = fv sfm
  cntms = toSeq $ Set.map (\(c,_) -> fApp c []) consts
  (consts,funcs) = herbfuns sfm


toSeq :: (SetLike set, Ord a) => set a -> Seq a
toSeq = toSetlike

toSetlike s =
    go s slEmpty
    where
      go s r =
          case slView s of
            Nothing -> r
            Just (x, s') -> go s' (slInsert x r)


{-
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
            (atom ~ AtomOf lit, v ~ VarOf lit, v ~ TVarOf term, term ~ TermOf atom, function ~ FunOf term,
             JustLiteral lit,
             HasApply atom,
             IsTerm term) =>
            (Set (Set lit) -> (lit -> lit) -> Set (Set lit) -> Set (Set lit))
         -> (Set (Set lit) -> Bool)
         -> Set (Set lit)
         -> Set term
         -> Set (function, Int)
         -> [VarOf lit]
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
        case tfn fl' of
          False -> Set.insert tup tried
          True -> herbloop mfn tfn fl0 cntms fns fvs n fl' (Set.insert tup tried) tups

-- | Hence a simple Gilmore-type procedure.
gilmore_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, v ~ VarOf lit, v ~ TVarOf term, function ~ FunOf term,
                 JustLiteral lit, Ord lit,
                 HasApply atom,
                 IsTerm term) =>
                Set (Set lit)
             -> Set term
             -> Set (function, Int)
             -> [VarOf lit]
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
           (atom ~ AtomOf fof, term ~ TermOf atom, v ~ VarOf fof, v ~ TVarOf term, function ~ FunOf term,
            IsFirstOrder fof, Ord fof,
            HasSkolem function v) =>
           fof -> Failing Int
gilmore fm =
  let (sfm :: Marked Propositional fof) = runSkolem (skolemize id ((.~.) (generalize fm)))
      fvs = Set.toList (fv sfm)
      (consts, fns) = herbfuns sfm
      cntms = Set.map (\ (c,_) -> fApp c []) consts in
  Set.size <$> gilmore_loop (simpdnf id sfm  :: Set (Set (Marked Literal (Marked Propositional fof)))) cntms fns fvs 0 (Set.singleton Set.empty) Set.empty Set.empty
{-
  let fvs = Set.toList (overatoms (\ a s -> Set.union s (fv (atomic a :: fof))) sfm (Set.empty))
      (consts,fns) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  gilmore_loop (simpdnf id sfm :: Set (Set (Marked Literal (Marked Propositional fof)))) cntms fns (fvs) 0 (Set.singleton Set.empty) Set.empty Set.empty >>= return . Set.size
-}
-}

#ifndef NOTESTS
-- | First example and a little tracing.
test01 :: Test
test01 =
    let label = "gilmore(" ++ prettyShow fm ++ ")"
        fm = [fof| ∃x. (∀y. (p(x) ==> p(y))) |]
        expected = 2 in
    TestLabel label $ TestCase $ assertEqual label expected (gilmore fm)

-- -------------------------------------------------------------------------
-- Quick example.
-- -------------------------------------------------------------------------

p24 =
    let label = "gilmore p24 (p. 160): " ++ prettyShow fm
        x = vt "x"
        p = pApp "P" :: [MyTerm] -> MyFormula
        q = pApp "Q" :: [MyTerm] -> MyFormula
        r = pApp "R" :: [MyTerm] -> MyFormula
        u = pApp "U" :: [MyTerm] -> MyFormula
        fm :: MyFormula
        fm = ((.~.)(exists "x" (u[x] .&. q[x]))) .&.
             (for_all "x" (p[x] .=>. q[x] .|. r[x])) .&.
             ((.~.)(exists ("x" :: V) (p[x] .=>. (exists "x" (q[x]))))) .&.
             (for_all "x" (q[x] .&. r[x] .=>. u[x])) .=>.
             (exists "x" (p[x] .&. r[x])) in
    TestLabel label $ TestCase $ assertEqual label 1 (gilmore fm)
{-

p24 :: Test
p24 =
     let label = "gilmore p24 (p. 160): " ++ prettyShow fm
         fm = [fof|~(exists x. (U(x) /\ Q(x))) /\
                    (forall x. (P(x) ==> Q(x) \/ R(x))) /\
                   ~(exists x. (P(x) ==> (exists x. Q(x)))) /\
                    (forall x. (Q(x) /\ R(x) ==> U(x)))
                       ==> (exists x. (P(x) /\ R(x)))|] in
    TestLabel label $ TestCase $ assertEqual label 1 (gilmore fm)
-}
{-
let p24 = gilmore
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;
-}

-- | Slightly less easy example.
p45fm =      [fof| (((forall x.
                      ((P(x) & (forall y. ((G(y) & H(x,y)) ==> J(x,y)))) ==>
                       (forall y. ((G(y) & H(x,y)) ==> R(y))))) &
                     ((~(exists y. (L(y) & R(y)))) &
                      (exists x.
                       (P(x) &
                        ((forall y. (H(x,y) ==> L(y))) &
                         (forall y. ((G(y) & H(x,y)) ==> J(x,y)))))))) ==>
                    (exists x. (P(x) & (~(exists y. (G(y) & H(x,y))))))) |]
p45 = TestLabel "gilmore p45" $ TestCase $ assertEqual "gilmore p45" 5 (gilmore p45fm)
{-
p45 =
    let label = "gilmore p45: " ++ prettyShow fm
        fm = [fof| (forall x. (P(x) & (forall y. (G(y) & H(x,y) ==> J(x,y))))
                     ==> (forall y. (G(y) & H(x,y) ==> R(y)))) &
                    (~(exists y. (L(y) & R(y)))) &
                    (exists x. (P(x) & (forall y. (H(x,y) ==> L(y))) /\
                                       (forall y. (G(y) & H(x,y) ==> J(x,y)))))
                    ==> (exists x. (P(x) & (~(exists y. (G(y) /\ H(x,y))))))
                 |] in
    TestLabel label $ TestCase $ assertEqual label 5 (gilmore fm)
-}
{-
0 ground instances tried; 1 items in list
0 ground instances tried; 1 items in list
1 ground instances tried; 13 items in list
1 ground instances tried; 13 items in list
2 ground instances tried; 57 items in list
3 ground instances tried; 84 items in list
4 ground instances tried; 405 items in list
-}
{-
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

dp_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf lit, v ~ TVarOf term,
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
               (atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf formula, v ~ TVarOf term,
                IsFirstOrder formula, Ord formula,
                HasSkolem function v) =>
               formula -> Int
davisputnam fm =
  let (sfm :: Marked Propositional formula) = runSkolem (skolemize id ((.~.)(generalize fm))) in
  let fvs = Set.toList (overatoms (\ a s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
      (consts,fns) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  Set.size $ dp_loop (simpcnf id sfm :: Set (Set (Marked Literal formula))) cntms fns fvs 0 Set.empty Set.empty Set.empty

{-
-- | Show how much better than the Gilmore procedure this can be.
START_INTERACTIVE;;
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;
-}

-- | Show how few of the instances we really need. Hence unification!
davisputnam' :: forall formula atom predicate term v function.
                (atom ~ AtomOf formula, predicate ~ PredOf atom, term ~ TermOf atom, function ~ FunOf term, v ~ VarOf formula, v ~ TVarOf term,
                 IsFirstOrder formula, Ord formula,
                 HasSkolem function v) =>
                formula -> formula -> formula -> Int
davisputnam' _ _ fm =
    let (sfm :: Marked Propositional formula) = runSkolem (skolemize id ((.~.)(generalize fm))) in
    let fvs = Set.toList (overatoms (\ (a :: AtomOf formula) s -> Set.union (fv (atomic a :: formula)) s) sfm Set.empty)
        consts :: Set (function, Arity)
        fns :: Set (function, Arity)
        (consts,fns) = herbfuns sfm in
    let cntms :: Set (TermOf (AtomOf formula))
        cntms = Set.map (\ (c,_) -> fApp c []) consts in
    Set.size $ dp_refine_loop (simpcnf id sfm :: Set (Set (Marked Literal formula))) cntms fns fvs 0 Set.empty Set.empty Set.empty

-- | Try to cut out useless instantiations in final result.
dp_refine_loop :: (atom ~ AtomOf lit, term ~ TermOf atom, v ~ VarOf lit, v ~ TVarOf term, function ~ FunOf term,
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
    dp_refine cjs0 fvs tups mempty
    where
      tups = dp_loop cjs0 cntms fns fvs n cjs tried tuples

dp_refine :: (HasApply atom, JustLiteral lit, Ord lit, IsTerm term,
              atom ~ AtomOf lit, term ~ TermOf atom, v ~ VarOf lit, v ~ TVarOf term) =>
             Set (Set lit) -> [v] -> Set [term] -> Set [term] -> Set [term]
dp_refine cjs0 fvs dknow need =
    case Set.minView dknow of
      Nothing -> need
      Just (cl, dknow') ->
          dp_refine cjs0 fvs dknow need'
              where
                mfn = (dp_mfn cjs0) . lsubst . (Map.fromList . zip fvs)
                need' = if dpll (Foldable.foldr mfn Set.empty (need <> dknow)) then Set.insert cl need else need
{-
          let mfn = dp_mfn cjs0 . lsubst . Map.fromList . zip fvs in
          dpll (Set.fold mfn Set.empty (Set.union need dknow')) >>= \ flag ->
          dp_refine cjs0 fvs dknow' (if flag then Set.insert cl need else need)
-}

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

#ifndef NOTESTS
testHerbrand :: Test
testHerbrand = TestLabel "Herbrand" (TestList [test01, p24, p45])
#endif
