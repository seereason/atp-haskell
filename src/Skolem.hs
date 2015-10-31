-- | Prenex and Skolem normal forms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Skolem
    ( -- * Simplify for predicate formulas
      simplify
    -- * Normal forms
    , nnf
    , pnf
    -- , functions
    -- , funcs
    -- * Skolem monad
    , SkolemM
    , runSkolem
    , SkolemT
    , runSkolemT
    , HasSkolem(toSkolem, fromSkolem)
    , skolems
    , askolemize
    , skolemize
    , specialize
    , simpdnf'
    , simpcnf'
#ifndef NOTESTS
    -- * Instances
    , Function(Fn, Skolem)
    , MyTerm, MyAtom, MyFormula
    -- * Tests
    , testSkolem
#endif
    ) where

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (runStateT, StateT)
import Data.List as List (map)
import Data.Map as Map (singleton)
import Data.Maybe (isJust)
import Data.Set as Set (empty, filter, isProperSubsetOf, map, member, Set, singleton, toAscList, union)
import FOL (exists, fApp, for_all, functions, fv, HasApply(TermOf, PredOf), IsFirstOrder, IsQuantified(VarOf, foldQuantified),
            IsTerm(TVarOf, FunOf), quant, Quant((:?:), (:!:)), subst, variant, vt)
import Formulas ((.~.), (.&.), (.|.), (.=>.), (.<=>.), BinOp((:&:), (:|:), (:=>:), (:<=>:)), IsFormula(AtomOf), negate, false, true, atomic)
import Lib (setAny, distrib)
import Prelude hiding (negate)
import Prop (convertToPropositional, foldPropositional', IsPropositional, JustPropositional, psimplify1, trivial)
#ifndef NOTESTS
import Data.Generics (Data, Typeable)
import Data.Monoid ((<>))
import Data.String (IsString(fromString))
import FOL (FOLEQ, Formula, IsFunction, pApp, Predicate, Term, V)
import Lib (Marked(Mark))
import Pretty (Expr, Pretty(pPrint), prettyShow, text)
import Prop (Propositional)
import Test.HUnit
#endif

-- | Routine simplification. Like "psimplify" but with quantifier clauses.
simplify :: (IsQuantified formula, HasApply atom, IsTerm term, atom ~ AtomOf formula, term ~ TermOf atom, v ~ VarOf formula, v ~ TVarOf term {-, atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term, IsFirstOrder formula-}) => formula -> formula
simplify fm =
    foldQuantified qu co ne (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = simplify1 (for_all x (simplify p))
      qu (:?:) x p = simplify1 (exists x (simplify p))
      ne p = simplify1 ((.~.) (simplify p))
      co p (:&:) q = simplify1 (simplify p .&. simplify q)
      co p (:|:) q = simplify1 (simplify p .|. simplify q)
      co p (:=>:) q = simplify1 (simplify p .=>. simplify q)
      co p (:<=>:) q = simplify1 (simplify p .<=>. simplify q)

simplify1 :: (IsQuantified formula, HasApply atom, IsTerm term, atom ~ AtomOf formula, term ~ TermOf atom, v ~ VarOf formula, v ~ TVarOf term {-atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
              IsFirstOrder formula-}) =>
             formula -> formula
simplify1 fm =
    foldQuantified qu (\_ _ _ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) fm
    where
      qu _ x p = if member x (fv p) then fm else p

#ifndef NOTESTS
-- | Concrete formula type for use in unit tests.
type MyTerm = Term Function V
type MyAtom = FOLEQ Predicate MyTerm
type MyFormula = Formula V MyAtom

--instance HasFunctions MyFormula Function where
--    funcs = quantifiedFuncs

instance IsFirstOrder MyFormula

-- Example.
test01 :: Test
test01 = TestCase $ assertEqual ("simplify (p. 140) " ++ prettyShow fm) expected input
    where input = prettyShow (simplify fm)
          expected = prettyShow ((for_all "x" (pApp "P" [vt "x"])) .=>. (pApp "Q" []) :: MyFormula)
          fm :: MyFormula
          fm = (for_all "x" (for_all "y" (pApp "P" [vt "x"] .|. (pApp "P" [vt "y"] .&. false)))) .=>. exists "z" (pApp "Q" [])
#endif

-- | Negation normal form for first order formulas
nnf :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
        IsFirstOrder formula) => formula -> formula
nnf = nnf1 . simplify

nnf1 :: IsQuantified formula => formula -> formula
nnf1 fm =
    foldQuantified qu co ne (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = quant (:!:) x (nnf1 p)
      qu (:?:) x p = quant (:?:) x (nnf1 p)
      ne p = foldQuantified quNot coNot neNot (\_ -> fm) (\_ -> fm) p
      co p (:&:) q = nnf1 p .&. nnf1 q
      co p (:|:) q = nnf1 p .|. nnf1 q
      co p (:=>:) q = nnf1 ((.~.) p) .|. nnf1 q
      co p (:<=>:) q = (nnf1 p .&. nnf1 q) .|. (nnf1 ((.~.) p) .&. nnf1 ((.~.) q))
      quNot (:!:) x p = quant (:?:) x (nnf1 ((.~.) p))
      quNot (:?:) x p = quant (:!:) x (nnf1 ((.~.) p))
      neNot p = nnf1 p
      coNot p (:&:) q = nnf1 ((.~.) p) .|. nnf1 ((.~.) q)
      coNot p (:|:) q = nnf1 ((.~.) p) .&. nnf1 ((.~.) q)
      coNot p (:=>:) q = nnf1 p .&. nnf1 ((.~.) q)
      coNot p (:<=>:) q = (nnf1 p .&. nnf1 ((.~.) q)) .|. (nnf1 ((.~.) p) .&. nnf1 q)

#ifndef NOTESTS
-- Example of NNF function in action.
test02 :: Test
test02 = TestCase $ assertEqual "nnf (p. 140)" expected input
    where p = "P"
          q = "Q"
          input = nnf fm
          expected = exists "x" ((.~.)(pApp p [vt "x"])) .|.
                     ((exists "y" (pApp q [vt "y"]) .&. exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))) .|.
                      (for_all "y" ((.~.)(pApp q [vt "y"])) .&.
                       for_all "z" (((.~.)(pApp p [vt "z"])) .|. ((.~.)(pApp q [vt "z"])))) :: MyFormula)
          fm :: MyFormula
          fm = (for_all "x" (pApp p [vt "x"])) .=>. ((exists "y" (pApp q [vt "y"])) .<=>. exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"]))
#endif

-- | Prenex normal form.
pnf :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
        IsFirstOrder formula) => formula -> formula
pnf = prenex . nnf . simplify

prenex :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
           IsFirstOrder formula) => formula -> formula
prenex fm =
    foldQuantified qu co (\ _ -> fm) (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co l (:&:) r = pullquants (prenex l .&. prenex r)
      co l (:|:) r = pullquants (prenex l .|. prenex r)
      co _ _ _ = fm

pullquants :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
               IsFirstOrder formula) => formula -> formula
pullquants fm =
    foldQuantified (\_ _ _ -> fm) pullQuantsCombine (\_ -> fm) (\_ -> fm) (\_ -> fm) fm
    where
      pullQuantsCombine l op r =
          case (getQuant l, op, getQuant r) of
            (Just ((:!:), vl, l'), (:&:), Just ((:!:), vr, r')) -> pullq (True,  True)  fm for_all (.&.) vl vr l' r'
            (Just ((:?:), vl, l'), (:|:), Just ((:?:), vr, r')) -> pullq (True,  True)  fm exists  (.|.) vl vr l' r'
            (Just ((:!:), vl, l'), (:&:), _)                    -> pullq (True,  False) fm for_all (.&.) vl vl l' r
            (_,                    (:&:), Just ((:!:), vr, r')) -> pullq (False, True)  fm for_all (.&.) vr vr l  r'
            (Just ((:!:), vl, l'), (:|:), _)                    -> pullq (True,  False) fm for_all (.|.) vl vl l' r
            (_,                    (:|:), Just ((:!:), vr, r')) -> pullq (False, True)  fm for_all (.|.) vr vr l  r'
            (Just ((:?:), vl, l'), (:&:), _)                    -> pullq (True,  False) fm exists  (.&.) vl vl l' r
            (_,                    (:&:), Just ((:?:), vr, r')) -> pullq (False, True)  fm exists  (.&.) vr vr l  r'
            (Just ((:?:), vl, l'), (:|:), _)                    -> pullq (True,  False) fm exists  (.|.) vl vl l' r
            (_,                    (:|:), Just ((:?:), vr, r')) -> pullq (False, True)  fm exists  (.|.) vr vr l  r'
            _                                                   -> fm
      getQuant = foldQuantified (\ op v f -> Just (op, v, f)) (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing)

pullq :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
          IsFirstOrder formula) =>
         (Bool, Bool)
      -> formula
      -> (v -> formula -> formula)
      -> (formula -> formula -> formula)
      -> v
      -> v
      -> formula
      -> formula
      -> formula
pullq (l,r) fm qu op x y p q =
  let z = variant x (fv fm) in
  let p' = if l then subst (Map.singleton x (vt z)) p else p
      q' = if r then subst (Map.singleton y (vt z)) q else q in
  qu z (pullquants (op p' q'))

#ifndef NOTESTS
-- Example.

test03 :: Test
test03 = TestCase $ assertEqual "pnf (p. 144)" (prettyShow expected) (prettyShow input)
    where p = "P"
          q = "Q"
          r = "R"
          input = pnf fm
          expected = exists "x" (for_all "z"
                                 ((((.~.)(pApp p [vt "x"])) .&. ((.~.)(pApp r [vt "y"]))) .|.
                                  ((pApp q [vt "x"]) .|.
                                   (((.~.)(pApp p [vt "z"])) .|.
                                    ((.~.)(pApp q [vt "z"])))))) :: MyFormula
          fm :: MyFormula
          fm = (for_all "x" (pApp p [vt "x"]) .|. (pApp r [vt "y"])) .=>.
               exists "y" (exists "z" ((pApp q [vt "y"]) .|. ((.~.)(exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"])))))
#endif

-- -------------------------------------------------------------------------
-- State monad for generating Skolem functions and constants.
-- -------------------------------------------------------------------------

-- | The OCaml code generates skolem functions by adding a prefix to
-- the variable name they are based on.  Here we have a more general
-- and type safe solution: we require that variables be instances of
-- class 'Skolem' which creates Skolem functions based on an integer.
-- This state value exists in the 'SkolemM' monad during skolemization
-- and tracks the next available number and the current list of
-- universally quantified variables.

-- | The Skolem monad
type SkolemM = StateT SkolemState Identity

data SkolemState
    = SkolemState
      { skolemCount :: Int
        -- ^ The next available Skolem number.
      , univQuant :: [String]
        -- ^ The variables which are universally quantified in the
        -- current scope, in the order they were encountered.  During
        -- Skolemization these are the parameters passed to the Skolem
        -- function.
      }

-- | The state associated with the Skolem monad.
newSkolemState :: SkolemState
newSkolemState
    = SkolemState
      { skolemCount = 1
      , univQuant = []
      }

-- | The Skolem monad transformer
type SkolemT m = StateT SkolemState m

-- | Run a computation in the Skolem monad.
runSkolem :: SkolemT Identity a -> a
runSkolem = runIdentity . runSkolemT

-- | Run a computation in a stacked invocation of the Skolem monad.
runSkolemT :: Monad m => SkolemT m a -> m a
runSkolemT action = (runStateT action) newSkolemState >>= return . fst

-- | Class of functions that include embedded Skolem functions
--
-- A Skolem function is created to eliminate an an existentially
-- quantified variable.  The idea is that if we have a predicate
-- @P[x,y,z]@, and @z@ is existentially quantified, then @P@ is only
-- satisfiable if there *exists* at least one @z@ that causes @P@ to
-- be true.  Therefore, we envision a function @sKz[x,y]@ whose value
-- is one of the z's that cause @P@ to be satisfied (if there are any;
-- if the formula is satisfiable there must be.)  Because we are
-- trying to determine if there is a satisfying triple @x, y, z@, the
-- Skolem function @sKz@ will have to be a function of @x@ and @y@, so
-- we make these parameters.  Now, if @P[x,y,z]@ is satisfiable, there
-- will be a function sKz which can be substituted in such that
-- @P[x,y,sKz[x,y]]@ is also satisfiable.  Thus, using this mechanism
-- we can eliminate all the formula's existential quantifiers and some
-- of its variables.
class HasSkolem function v | function -> v where
    toSkolem :: v -> function
    fromSkolem :: function -> Maybe v

-- | Extract the skolem functions from a formula.
skolems :: (atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term, v ~ TVarOf term,
            HasSkolem function v, HasApply atom, Ord function) => IsFormula formula => formula -> Set function
skolems = Set.filter (isJust . fromSkolem) . Set.map fst . functions

-- | Core Skolemization function.
--
-- Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the SkolemT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
           IsFirstOrder formula,
           HasSkolem function v, Monad m) =>
          formula -> SkolemT m formula
skolem fm =
    foldQuantified qu co ne tf (return . atomic) fm
    where
      qu (:?:) y p =
          do let xs = fv fm
             let fx = fApp (toSkolem y) (List.map vt (Set.toAscList xs))
             skolem (subst (Map.singleton y fx) p)
      qu (:!:) x p = skolem p >>= return . for_all x
      co l (:&:) r = skolem2 (.&.) l r
      co l (:|:) r = skolem2 (.|.) l r
      co _ _ _ = return fm
      ne _ = return fm
      tf True = return true
      tf False = return false

skolem2 :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
            IsFirstOrder formula,
            HasSkolem function v, Monad m) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- | Overall Skolemization function.
askolemize :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
               IsFirstOrder formula,
               HasSkolem function v, Monad m) =>
              formula -> SkolemT m formula
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.  For this reason we can safely convert to any
-- instance of IsPropositional.
specialize :: (IsQuantified fof, IsPropositional pf, JustPropositional pf) => (AtomOf fof -> AtomOf pf) -> fof -> pf
specialize ca fm =
    convertToPropositional (error "specialize failure") ca (specialize' fm)
    where
      specialize' p = foldQuantified qu (\_ _ _ -> p) (\_ -> p) (\_ -> p) (\_ -> p) p
      qu (:!:) _ p = specialize' p
      qu _ _ _ = fm

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of IsPropositional.
skolemize :: (atom ~ AtomOf formula, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
              IsFirstOrder formula,
              HasSkolem function v,
              IsPropositional pf, JustPropositional pf,
              Monad m) =>
             (AtomOf formula -> AtomOf pf) -> formula -> StateT SkolemState m pf
skolemize ca fm = (specialize ca . pnf) <$> askolemize fm

#ifndef NOTESTS
-- | A function type that is an instance of HasSkolem
data Function
    = Fn String
    | Skolem V
    deriving (Eq, Ord, Data, Typeable, Show)

instance IsFunction Function

instance IsString Function where
    fromString = Fn

instance Show (Marked Expr Function) where
    show (Mark (Fn s)) = show s
    show (Mark (Skolem v)) = "(toSkolem " ++ show v ++ ")"

instance Pretty Function where
    pPrint (Fn s) = text s
    pPrint (Skolem v) = text "sK" <> pPrint v

instance HasSkolem Function V where
    toSkolem = Skolem
    fromSkolem (Skolem v) = Just v
    fromSkolem _ = Nothing

-- Example.

test04 :: Test
test04 = TestCase $ assertEqual "skolemize 1 (p. 150)" expected input
    where input = runSkolem (skolemize id fm) :: Marked Propositional MyFormula
          fm :: MyFormula
          fm = exists "y" (pApp ("<") [vt "x", vt "y"] .=>.
                           for_all "u" (exists "v" (pApp ("<") [fApp "*" [vt "x", vt "u"],  fApp "*" [vt "y", vt "v"]])))
          expected = ((.~.)(pApp ("<") [vt "x",fApp (Skolem "y") [vt "x"]])) .|.
                     (pApp ("<") [fApp "*" [vt "x",vt "u"],fApp "*" [fApp (Skolem "y") [vt "x"],fApp (Skolem "v") [vt "u",vt "x"]]])

test05 :: Test
test05 = TestCase $ assertEqual "skolemize 2 (p. 150)" expected input
    where p = "P"
          q = "Q"
          input = runSkolem (skolemize id fm) :: Marked Propositional MyFormula
          fm :: MyFormula
          fm = for_all "x" ((pApp p [vt "x"]) .=>.
                            (exists "y" (exists "z" ((pApp q [vt "y"]) .|.
                                                     ((.~.)(exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))))))))
          expected = ((.~.)(pApp p [vt "x"])) .|.
                     ((pApp q [fApp (Skolem "y") []]) .|.
                      (((.~.)(pApp p [vt "z"])) .|.
                       ((.~.)(pApp q [vt "z"]))))
#endif

-- Versions of the normal form functions that leave quantifiers in place.
simpdnf' :: (atom ~ AtomOf fof, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf fof, v ~ TVarOf term, function ~ FunOf term,
             IsFirstOrder fof, Ord fof) => fof -> Set (Set fof)
simpdnf' fm =
    {-t2 $-}
    foldQuantified (\_ _ _ -> go) (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) ({-t1-}fm)
    where
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf' (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs
      -- t1 x = trace ("simpdnf' (" ++ prettyShow x) x
      -- t2 x = trace ("simpdnf' (" ++ prettyShow fm ++ ") -> " ++ prettyShow x) x

purednf' :: (IsQuantified fof, Ord fof) => fof -> Set (Set fof)
purednf' fm =
    {-t4 $-}
    foldPropositional' ho co (\_ -> lf fm) (\_ -> lf fm) (\_ -> lf fm) ({-t3-} fm)
    where
      lf = Set.singleton . Set.singleton
      ho _ = lf fm
      co p (:&:) q = distrib (purednf' p) (purednf' q)
      co p (:|:) q = union (purednf' p) (purednf' q)
      co _ _ _ = lf fm
      -- t3 x = trace ("purednf' (" ++ prettyShow x) x
      -- t4 x = trace ("purednf' (" ++ prettyShow fm ++ ") -> " ++ prettyShow x) x

simpcnf' :: (atom ~ AtomOf fof, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf fof, v ~ TVarOf term, function ~ FunOf term,
             IsFirstOrder fof, Ord fof) => fof -> Set (Set fof)
simpcnf' fm =
    foldQuantified (\_ _ _ -> go) (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      go = let cjs = Set.filter (not . trivial) (purecnf' fm) in
           Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

purecnf' :: (atom ~ AtomOf fof, term ~ TermOf atom, predicate ~ PredOf atom, v ~ VarOf fof, v ~ TVarOf term, function ~ FunOf term,
             IsFirstOrder fof, Ord fof) => fof -> Set (Set fof)
purecnf' fm = Set.map (Set.map negate) (purednf' (nnf ((.~.) fm)))

#ifndef NOTESTS
testSkolem :: Test
testSkolem = TestLabel "Skolem" (TestList [test01, test02, test03, test04, test05])
#endif
