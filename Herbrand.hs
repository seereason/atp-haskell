-- | Relation between FOL and propositonal logic; Herbrand theorem.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, GADTs, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Herbrand where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import Data.Set as Set
import Data.String (IsString(..))
import Lib (allpairs, distrib')
import DP (dpll)
import FOL (IsFirstOrder, IsTerm, fApp, subst, IsAtom, fv, generalize, exists, for_all, pApp, V, vt)
import Formulas ((.~.), foldAtoms, atomic, (.=>.), (.&.), (.|.))
import Lit (IsLiteral)
import Pretty (prettyShow)
import Prop (IsPropositional, eval, trivial, simpcnf, simpdnf)
import Skolem (Arity, functions, HasSkolem, runSkolem, skolemize, MyFormula, MyTerm)
import Test.HUnit

-- | Propositional valuation.
pholds :: (IsPropositional formula atom, Ord atom) => (atom -> Bool) -> formula -> Bool
pholds d fm = eval fm d

-- | Get the constants for Herbrand base, adding nullary one if necessary.
herbfuns :: (IsFirstOrder fof atom v, IsAtom atom predicate term, IsTerm term v function, IsString function, Ord function) =>
            fof -> (Set (function, Arity), Set (function, Arity))
herbfuns fm =
  let (cns,fns) = Set.partition (\ (_,ar) -> ar == 0) (functions fm) in
  if Set.null cns then (Set.singleton (fromString "c",0),fns) else (cns,fns)

-- | Enumeration of ground terms and m-tuples, ordered by total fns.
groundterms :: forall term v f. (IsTerm term v f) =>
               Set term -> Set (f, Arity) -> Int -> Set term
groundterms cntms _ 0 = cntms
groundterms cntms funcs n =
    Set.fold terms Set.empty funcs
    where
      terms (f,m) l = Set.union (Set.map (fApp f) (groundtuples cntms funcs (n - 1) m)) l

groundtuples :: forall term v f. (IsTerm term v f) =>
                Set term -> Set (f, Int) -> Int -> Int -> Set [term]
groundtuples _ _ 0 0 = Set.singleton []
groundtuples _ _ _ 0 = Set.empty
groundtuples cntms funcs n m =
    Set.fold tuples Set.empty (Set.fromList [0 .. n])
    where
      tuples k l = Set.union (allpairs (:) (groundterms cntms funcs k) (groundtuples cntms funcs (n - k) (m - 1))) l

-- | Iterate modifier "mfn" over ground terms till "tfn" fails.
herbloop :: forall lit v term formula atom predicate function. (IsTerm term v function, IsFirstOrder formula atom v, IsAtom atom predicate term) =>
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
{-
  print_string(string_of_int(length tried) ++ " ground instances tried; " ++
               string_of_int(length fl) ++ " items in list")
  print_newline();
-}
  case Set.minView tuples of
    Nothing ->
          let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtups
    Just (tup, tups) ->
        let fpf' = Map.fromList (zip fvs tup) in
        let fl' = mfn fl0 (subst fpf' {-:: lit-}) fl in
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
gilmore_loop :: forall lit atom term v function predicate.
                (IsFirstOrder lit atom v, IsLiteral lit atom, IsTerm term v function, IsAtom atom predicate term, Ord lit, Ord predicate) =>
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
      mfn djs0 ifn djs = Set.filter (not . trivial) (distrib' (Set.map (Set.map ifn) djs0) djs)

gilmore :: forall fof atom predicate term function v.
           (Ord predicate,
            IsLiteral fof atom,
            IsTerm term v function,
            IsFirstOrder fof atom v,
            IsAtom atom predicate term,
            HasSkolem function v, Ord function, IsString function) =>
           fof
        -> Failing Int
gilmore fm =
  let sfm = runSkolem (skolemize ((.~.) (generalize fm))) in
  let (fvs :: [v]) = Set.toList (foldAtoms (\ (a :: atom) (s :: Set v) -> Set.union s (fv (atomic a :: fof))) sfm (Set.empty))
      (consts :: Set (function, Int),funcs :: Set (function, Int)) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c []) consts in
  gilmore_loop (simpdnf sfm {-:: Set (Set pf)-}) cntms funcs (fvs) 0 Set.empty Set.empty Set.empty >>= return . Set.size

-- | First example and a little tracing.
test01 :: Test
test01 =
    let fm = exists "x" (for_all "y" (pApp "p" [vt "x"] .=>. pApp "p" [vt "y"])) :: MyFormula
        sfm = runSkolem (skolemize ((.~.) fm)) in
    TestCase (assertEqual ("gilmore 1: " ++ prettyShow fm) (Success 2) (gilmore fm))

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


-- | The Davis-Putnam procedure for first order logic.
dp_mfn :: Ord b => Set (Set a) -> (a -> b) -> Set (Set b) -> Set (Set b)
dp_mfn cjs0 ifn cjs = Set.union (Set.map (Set.map ifn) cjs0) cjs

dp_loop :: forall lit atom v term predicate function. (IsFirstOrder lit atom v, IsLiteral lit atom, IsTerm term v function, IsAtom atom predicate term, Ord lit) =>
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

davisputnam :: forall fof atom term v lit predicate function.
               (IsLiteral fof atom,
                IsFirstOrder fof atom v,
                IsPropositional lit atom,
                IsLiteral lit atom,
                IsTerm term v function,
                IsAtom atom predicate term,
                IsString function,
                HasSkolem function v,
                Ord lit, Ord function) =>
               lit -> (atom -> Set (function, Int)) -> fof -> Failing Int
davisputnam _ fa fm =
  let (sfm {-:: lit-}) = runSkolem (skolemize ((.~.)(generalize fm))) in
  let fvs = Set.toList (foldAtoms (\ (a :: atom) s -> Set.union (fv (atomic a :: fof)) s) sfm Set.empty)
      (consts,funcs) = herbfuns sfm in
  let cntms = Set.map (\ (c,_) -> fApp c [] :: term) consts in
  dp_loop (simpcnf sfm :: Set (Set fof)) cntms funcs fvs 0 Set.empty Set.empty Set.empty >>= return . Set.size

{-
-- | Show how much better than the Gilmore procedure this can be.
START_INTERACTIVE;;
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;
-}

-- | Try to cut out useless instantiations in final result.
dp_refine :: (IsLiteral lit atom, IsTerm term v function,
              IsFirstOrder lit atom v, IsAtom atom predicate term) =>
             Set (Set lit) -> [v] -> Set [term] -> Set [term] -> Failing (Set [term])
dp_refine cjs0 fvs dknow need =
    case Set.minView dknow of
      Nothing -> Success need
      Just (cl, dknow') ->
          let mfn = dp_mfn cjs0 . subst . Map.fromList . zip fvs in
          dpll (Set.fold mfn Set.empty (Set.union need dknow')) >>= \ flag ->
          if flag then return (Set.insert cl need) else return need >>=
          dp_refine cjs0 fvs dknow'

dp_refine_loop :: forall v term predicate function lit atom.
                  (IsLiteral lit atom,
                   IsTerm term v function,
                   IsFirstOrder lit atom v,
                   IsAtom atom predicate term) =>
                  Set (Set lit)
               -> Set term
               -> Set (function, Int)
               -> [v]
               -> Int
               -> Set (Set lit)
               -> Set [term]
               -> Set [term]
               -> Failing (Set [term])
dp_refine_loop cjs0 cntms funcs fvs n cjs tried tuples =
    dp_loop cjs0 cntms funcs fvs n cjs tried tuples >>= \ tups ->
    dp_refine cjs0 fvs tups Set.empty

-- | Show how few of the instances we really need. Hence unification!
davisputnam' :: forall fof atom predicate term lit v f pf.
                (pf ~ fof, fof ~ lit,
                 IsFirstOrder fof atom v,
                 IsLiteral lit atom,
                 IsPropositional pf atom, -- Formula pf atom,
                 IsTerm term v f,
                 IsAtom atom predicate term,
                 IsString f, HasSkolem f v, Ord f) =>
                lit -> pf -> fof -> Failing Int
davisputnam' _ _ fm =
    let (sfm :: pf) = runSkolem (skolemize ((.~.)(generalize fm))) in
    let fvs = Set.toList (foldAtoms (\ (a :: atom) s -> Set.union (fv (atomic a :: fof)) s) sfm Set.empty)
        (consts,funcs) = herbfuns sfm in
    let cntms = Set.map (\ (c,_) -> fApp c []) consts in
    dp_refine_loop (simpcnf sfm :: Set.Set (Set.Set lit)) cntms funcs fvs 0 Set.empty Set.empty Set.empty >>= return . Set.size

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

tests :: Test
tests = TestList [test01, test02]
