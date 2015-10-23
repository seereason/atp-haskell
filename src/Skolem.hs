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
import Data.Generics (Data, Typeable)
import Data.List as List (map)
import Data.Map as Map (singleton)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, isProperSubsetOf, map, member, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import FOL (exists, fApp, for_all, fv, IsFirstOrder, IsFunction, IsQuantified(foldQuantified),
            pApp, propositionalFromQuantified, quant, Quant((:?:), (:!:)), subst, variant, vt)
#ifndef NOTESTS
import FOL (Formula, Term, V, FOL, Predicate)
#endif
import Formulas (Combination(BinOp), BinOp ((:&:), (:|:), (:=>:), (:<=>:)), (.~.), (.&.), (.|.), (.=>.), (.<=>.), negate, false, true, atomic)
import Lib (setAny, distrib)
import Prelude hiding (negate)
import Pretty (Pretty(pPrint), prettyShow, text)
import Prop (IsPropositional, JustPropositional, Marked, Propositional, psimplify1, trivial)
import Test.HUnit

-- | Routine simplification. Like "psimplify" but with quantifier clauses.
simplify :: IsFirstOrder formula atom predicate term v function => formula -> formula
simplify fm =
    foldQuantified qu co ne (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = simplify1 (for_all x (simplify p))
      qu (:?:) x p = simplify1 (exists x (simplify p))
      ne p = simplify1 ((.~.) (simplify p))
      co (BinOp p (:&:) q) = simplify1 (simplify p .&. simplify q)
      co (BinOp p (:|:) q) = simplify1 (simplify p .|. simplify q)
      co (BinOp p (:=>:) q) = simplify1 (simplify p .=>. simplify q)
      co (BinOp p (:<=>:) q) = simplify1 (simplify p .<=>. simplify q)

simplify1 :: IsFirstOrder formula atom predicate term v function =>
             formula -> formula
simplify1 fm =
    foldQuantified qu co ne (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) fm
    where
      qu _ x p = if member x (fv p) then fm else p
      -- If psimplify1 sees a negation it looks at its argument, so here we
      -- make sure that argument isn't a quantifier which would cause an error.
      ne p = foldQuantified (\_ _ _ -> fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) p
      co _ = psimplify1 fm

#ifndef NOTESTS
-- | Concrete types for use in unit tests.
type MyTerm = Term Function V
type MyAtom = FOL Predicate MyTerm
type MyFormula = Formula V MyAtom

--instance HasFunctions MyFormula Function where
--    funcs = quantifiedFuncs

instance IsFirstOrder MyFormula MyAtom Predicate MyTerm V Function

-- Example.
test01 :: Test
test01 = TestCase $ assertEqual ("simplify (p. 140) " ++ prettyShow fm) expected input
    where input = prettyShow (simplify fm)
          expected = prettyShow ((for_all "x" (pApp "P" [vt "x"])) .=>. (pApp "Q" []) :: MyFormula)
          fm :: MyFormula
          fm = (for_all "x" (for_all "y" (pApp "P" [vt "x"] .|. (pApp "P" [vt "y"] .&. false)))) .=>. exists "z" (pApp "Q" [])
#endif

-- | Negation normal form for first order formulas
nnf :: IsFirstOrder formula atom predicate term v function => formula -> formula
nnf = nnf1 . simplify

nnf1 :: (IsQuantified formula atom v) => formula -> formula
nnf1 fm =
    foldQuantified qu co ne (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = quant (:!:) x (nnf1 p)
      qu (:?:) x p = quant (:?:) x (nnf1 p)
      ne p = foldQuantified quNot coNot neNot (\_ -> fm) (\_ -> fm) p
      co (BinOp p (:&:) q) = nnf1 p .&. nnf1 q
      co (BinOp p (:|:) q) = nnf1 p .|. nnf1 q
      co (BinOp p (:=>:) q) = nnf1 ((.~.) p) .|. nnf1 q
      co (BinOp p (:<=>:) q) = (nnf1 p .&. nnf1 q) .|. (nnf1 ((.~.) p) .&. nnf1 ((.~.) q))
      quNot (:!:) x p = quant (:?:) x (nnf1 ((.~.) p))
      quNot (:?:) x p = quant (:!:) x (nnf1 ((.~.) p))
      neNot p = nnf1 p
      coNot (BinOp p (:&:) q) = nnf1 ((.~.) p) .|. nnf1 ((.~.) q)
      coNot (BinOp p (:|:) q) = nnf1 ((.~.) p) .&. nnf1 ((.~.) q)
      coNot (BinOp p (:=>:) q) = nnf1 p .&. nnf1 ((.~.) q)
      coNot (BinOp p (:<=>:) q) = (nnf1 p .&. nnf1 ((.~.) q)) .|. (nnf1 ((.~.) p) .&. nnf1 q)

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
pnf :: IsFirstOrder formula atom predicate term v function =>
       formula -> formula
pnf = prenex . nnf . simplify

prenex :: IsFirstOrder formula atom predicate term v function => formula -> formula
prenex fm =
    foldQuantified qu co (\ _ -> fm) (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co (BinOp l (:&:) r) = pullquants (prenex l .&. prenex r)
      co (BinOp l (:|:) r) = pullquants (prenex l .|. prenex r)
      co _ = fm

pullquants :: IsFirstOrder formula atom predicate term v function => formula -> formula
pullquants fm =
    foldQuantified (\_ _ _ -> fm) pullQuantsCombine (\_ -> fm) (\_ -> fm) (\_ -> fm) fm
    where
      pullQuantsCombine (BinOp l op r) =
          case (getQuant l, op, getQuant r) of
            (Just ((:!:), vl, l'), (:&:), Just ((:!:), vr, r')) -> pullq (True,  True)  fm for_all (.&.) vl vr l' r'
            (Just ((:?:), vl, l'), (:|:), Just ((:?:), vr, r')) -> pullq (True,  True)  fm exists  (.|.) vl vr l' r'
            (Just ((:!:), vl, l'), (:&:), _)                     -> pullq (True,  False) fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just ((:!:), vr, r')) -> pullq (False, True)  fm for_all (.&.) vr vr l  r'
            (Just ((:!:), vl, l'), (:|:), _)                     -> pullq (True,  False) fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just ((:!:), vr, r')) -> pullq (False, True)  fm for_all (.|.) vr vr l  r'
            (Just ((:?:), vl, l'), (:&:), _)                     -> pullq (True,  False) fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just ((:?:), vr, r')) -> pullq (False, True)  fm exists  (.&.) vr vr l  r'
            (Just ((:?:), vl, l'), (:|:), _)                     -> pullq (True,  False) fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just ((:?:), vr, r')) -> pullq (False, True)  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm
      getQuant = foldQuantified (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing)

pullq :: IsFirstOrder formula atom predicate term v function =>
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
type SkolemM v term = StateT SkolemState Identity

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
-- Skolem functions are created to replace an an existentially
-- quantified variable.  The idea is that if we have a predicate
-- @P[x,y,z]@, and @z@ is existentially quantified, then @P@ is
-- satisfiable if there is at least one @z@ that causes @P@ to be
-- true.  We postulate a skolem function @sKz[x,y]@ whose value is one
-- of the z's that cause @P@ to be satisfied.  The value of @sKz@ will
-- depend on @x@ and @y@, so we make these parameters.  Thus we have
-- eliminated existential quantifiers and obtained the formula
-- @P[x,y,sKz[x,y]]@.
class HasSkolem function var | function -> var where
    toSkolem :: var -> function
    fromSkolem :: function -> Maybe var

-- | Core Skolemization function.
--
-- Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the SkolemT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (IsFirstOrder formula atom predicate term v function,
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
      co (BinOp l (:&:) r) = skolem2 (.&.) l r
      co (BinOp l (:|:) r) = skolem2 (.|.) l r
      co _ = return fm
      ne _ = return fm
      tf True = return true
      tf False = return false

skolem2 :: (IsFirstOrder formula atom predicate term v function,
            HasSkolem function v, Monad m) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- | Overall Skolemization function.
askolemize :: (IsFirstOrder formula atom predicate term v function,
               HasSkolem function v, Monad m) =>
              formula -> SkolemT m formula
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.  For this reason we can safely convert to any
-- instance of IsPropositional.
specialize :: (IsQuantified fof atom1 v, IsPropositional pf atom2) => (atom1 -> atom2) -> fof -> pf
specialize ca fm =
    propositionalFromQuantified ca (specialize' fm)
    where
      specialize' p = foldQuantified qu (\_ -> p) (\_ -> p) (\_ -> p) (\_ -> p) p
      qu (:!:) _ p = specialize' p
      qu _ _ _ = fm

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of IsPropositional.
skolemize :: (IsFirstOrder formula atom predicate term v function,
              HasSkolem function v,
              IsPropositional pf atom2, JustPropositional pf, Monad m) =>
             (atom -> atom2) -> formula -> StateT SkolemState m pf
skolemize ca fm = (specialize ca . pnf) <$> askolemize fm

#ifndef NOTESTS
-- | A function type that is an instance of HasSkolem
data Function
    = Fn String
    | Skolem V
    deriving (Eq, Ord, Data, Typeable)

instance IsFunction Function

instance IsString Function where
    fromString = Fn

instance Show Function where
    show (Fn s) = show s
    show (Skolem v) = "(toSkolem " ++ show v ++ ")"

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
simpdnf' :: IsFirstOrder formula atom predicate term v function => formula -> Set (Set formula)
simpdnf' fm =
    {-t2 $-}
    foldQuantified (\_ _ _ -> go) (\_ -> go) (\_ -> go) tf (\_ -> go) ({-t1-} fm)
    where
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf' (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs
      -- t1 x = trace ("simpdnf' (" ++ prettyShow x) x
      -- t2 x = trace ("simpdnf' (" ++ prettyShow fm ++ ") -> " ++ prettyShow x) x

purednf' :: IsQuantified formula atom v => formula -> Set (Set formula)
purednf' fm =
    {-t4 $-}
    foldQuantified qu co (\_ -> lf fm) (\_ -> lf fm) (\_ -> lf fm) ({-t3-} fm)
    where
      lf = Set.singleton . Set.singleton
      qu _ _ _ = lf fm
      co (BinOp p (:&:) q) = distrib (purednf' p) (purednf' q)
      co (BinOp p (:|:) q) = union (purednf' p) (purednf' q)
      co _ = lf fm
      -- t3 x = trace ("purednf' (" ++ prettyShow x) x
      -- t4 x = trace ("purednf' (" ++ prettyShow fm ++ ") -> " ++ prettyShow x) x

simpcnf' :: (IsFirstOrder formula atom predicate term v function) => formula -> Set (Set formula)
simpcnf' fm =
    foldQuantified (\_ _ _ -> go) (\_ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      go = let cjs = Set.filter (not . trivial) (purecnf' fm) in
           Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

purecnf' :: (IsFirstOrder formula atom predicate term v function) => formula -> Set (Set formula)
purecnf' fm = Set.map (Set.map negate) (purednf' (nnf ((.~.) fm)))

#ifndef NOTESTS
testSkolem :: Test
testSkolem = TestLabel "Skolem" (TestList [test01, test02, test03, test04, test05])
#endif
