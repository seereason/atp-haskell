{-# LANGUAGE CPP, FlexibleContexts, FunctionalDependencies, GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
-- | Prenex and Skolem normal forms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
module Skolem
    ( -- * Simplify for predicate formulas
      simplify
    -- Predicate Application
    , pApp
    -- * Normal forms
    , nnf
    , pnf
    , functions
    -- * Skolem monad
    , SkolemM
    , runSkolem
    , runSkolemT
    , Skolem(toSkolem, fromSkolem)
    , askolemize
    , skolemize
    , Function(Fn, Skolem)
    , MyAtom, MyFormula
    -- * Tests
    , tests
    ) where

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (runStateT, StateT)
import Data.Map as Map (singleton)
import Data.Monoid ((<>))
import Data.Set as Set (member, Set, toAscList)
import Data.String (IsString(fromString))
import FOL hiding (tests)
import Formulas
--import Lib
import Prop hiding (nnf, tests)
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), prettyShow, text)

-- | Routine simplification. Like "psimplify" but with quantifier clauses.
simplify1 :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
             formula -> formula
simplify1 fm =
    foldFirstOrder qu co (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) fm
    where
      qu _ x p = if member x (fv p) then fm else p
      -- If psimplify1 sees a negation it looks at its argument, so here we
      -- make sure that argument isn't a quantifier which would cause an error.
      co ((:~:) p) = foldFirstOrder (\_ _ _ -> fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) p
      co _ = psimplify1 fm

simplify :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
            formula -> formula
simplify fm =
    foldFirstOrder qu co (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = simplify1 (for_all x (simplify p))
      qu (:?:) x p = simplify1 (exists x (simplify p))
      co ((:~:) p) = simplify1 ((.~.) (simplify p))
      co (BinOp p (:&:) q) = simplify1 (simplify p .&. simplify q)
      co (BinOp p (:|:) q) = simplify1 (simplify p .|. simplify q)
      co (BinOp p (:=>:) q) = simplify1 (simplify p .=>. simplify q)
      co (BinOp p (:<=>:) q) = simplify1 (simplify p .<=>. simplify q)

-- Example.
test01 :: Test
test01 = TestCase $ assertEqual ("simplify (p. 140) " ++ prettyShow fm) expected input
    where input = prettyShow (simplify fm)
          expected = prettyShow ((for_all "x" (pApp "P" [vt "x"])) .=>. (pApp "Q" []) :: Formula (FOL Predicate (Term FName V)))
          fm :: Formula (FOL Predicate (Term FName V))
          fm = (for_all "x" (for_all "y" (pApp "P" [vt "x"] .|. (pApp "P" [vt "y"] .&. false)))) .=>. exists "z" (pApp "Q" [])

-- | Negation normal form.
nnf :: (FirstOrderFormula formula atom v) => formula -> formula
nnf fm =
    foldFirstOrder qu co (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) x p = quant (:!:) x (nnf p)
      qu (:?:) x p = quant (:?:) x (nnf p)
      co ((:~:) p) = foldFirstOrder quNot coNot (\_ -> fm) (\_ -> fm) p
      co (BinOp p (:&:) q) = nnf p .&. nnf q
      co (BinOp p (:|:) q) = nnf p .|. nnf q
      co (BinOp p (:=>:) q) = nnf ((.~.) p) .|. nnf q
      co (BinOp p (:<=>:) q) = (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      quNot (:!:) x p = quant (:?:) x (nnf ((.~.) p))
      quNot (:?:) x p = quant (:!:) x (nnf ((.~.) p))
      coNot ((:~:) p) = nnf p
      coNot (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      coNot (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      coNot (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      coNot (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. (nnf ((.~.) p) .&. nnf q)

-- Example of NNF function in action.
test02 :: Test
test02 = TestCase $ assertEqual "nnf (p. 140)" expected input
    where p = "P"
          q = "Q"
          input = nnf fm
          expected = exists "x" ((.~.)(pApp p [vt "x"])) .|.
                     ((exists "y" (pApp q [vt "y"]) .&. exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))) .|.
                      (for_all "y" ((.~.)(pApp q [vt "y"])) .&.
                       for_all "z" (((.~.)(pApp p [vt "z"])) .|. ((.~.)(pApp q [vt "z"])))) :: Formula (FOL Predicate (Term FName V)))
          fm :: Formula (FOL Predicate (Term FName V))
          fm = (for_all "x" (pApp p [vt "x"])) .=>. ((exists "y" (pApp q [vt "y"])) .<=>. exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"]))

-- | Prenex normal form.
pullquants :: forall formula atom term predicate function v.
              (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) => formula -> formula
pullquants fm =
    foldFirstOrder (\_ _ _ -> fm) pullQuantsCombine (\_ -> fm) (\_ -> fm) fm
    where
      pullQuantsCombine :: Combination formula -> formula
      pullQuantsCombine ((:~:) _) = fm
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
      getQuant = foldFirstOrder (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing)

pullq :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
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

prenex :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) => formula -> formula
prenex fm =
    foldFirstOrder qu co (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co (BinOp l (:&:) r) = pullquants (prenex l .&. prenex r)
      co (BinOp l (:|:) r) = pullquants (prenex l .|. prenex r)
      co _ = fm

pnf :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function) =>
       formula -> formula
pnf fm = prenex (nnf (simplify fm))

-- Example.

test03 :: Test
test03 = TestCase $ assertEqual "pnf (p. 144)" expected input
    where p = "P"
          q = "Q"
          r = "R"
          input = pnf fm
          expected = exists "x" (for_all "z"
                                 ((((.~.)(pApp p [vt "x"])) .&. ((.~.)(pApp r [vt "y"]))) .|.
                                  ((pApp q [vt "x"]) .|.
                                   (((.~.)(pApp p [vt "z"])) .|.
                                    ((.~.)(pApp q [vt "z"])))))) :: Formula (FOL Predicate (Term Function V))
          fm :: Formula (FOL Predicate (Term Function V))
          fm = (for_all "x" (pApp p [vt "x"]) .|. (pApp r [vt "y"])) .=>.
               exists "y" (exists "z" ((pApp q [vt "y"]) .|. ((.~.)(exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"])))))


-- | Get the functions in a term and formula.
functions :: (FirstOrderFormula formula atom v, Ord function) =>
             (atom -> Set (function, Int)) -> formula -> Set (function, Int)
functions fa fm =
    foldFirstOrder qu co (\_ -> mempty) fa fm
    where
      qu _ _ p = functions fa p
      co ((:~:) p) = functions fa p
      co (BinOp p _ q) = functions fa p <> functions fa q

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
class Skolem function var | function -> var where
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
skolem :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function, Skolem function v, Monad m) =>
          formula -> SkolemT m formula
skolem fm =
    foldFirstOrder qu co tf (return . atomic) fm
    where
      qu (:?:) y p =
          do let xs = fv fm
             let fx = fApp (toSkolem y) (map vt (Set.toAscList xs))
             skolem (subst (Map.singleton y fx) p)
      qu (:!:) x p = skolem p >>= return . for_all x
      co (BinOp l (:&:) r) = skolem2 (.&.) l r
      co (BinOp l (:|:) r) = skolem2 (.|.) l r
      co _ = return fm
      tf True = return true
      tf False = return false

skolem2 :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function, Skolem function v, Monad m) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- | Overall Skolemization function.
askolemize :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function, Skolem function v, Monad m) =>
              formula -> SkolemT m formula
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.
specialize :: FirstOrderFormula r atom v => r -> r
specialize fm =
    foldFirstOrder qu (\_ -> fm) (\_ -> fm) (\_ -> fm) fm
    where
      qu (:!:) _ p = specialize p
      qu _ _ _ = fm

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of PropositionalFormula.
skolemize :: (FirstOrderFormula formula atom v, Atoms atom predicate term, Terms term v function, Skolem function v, Monad m) =>
             formula -> StateT SkolemState m formula
skolemize fm = (specialize . pnf) <$> askolemize fm

-- | A function type that is an instance of Skolem
data Function
    = Fn String
    | Skolem V
    deriving (Eq, Ord)

instance IsString Function where
    fromString = Fn

instance Show Function where
    show (Fn s) = show s
    show (Skolem v) = "(toSkolem " ++ show v ++ ")"

instance Pretty Function where
    pPrint (Fn s) = text s
    pPrint (Skolem v) = text "sK" <> pPrint v

instance Skolem Function V where
    toSkolem = Skolem
    fromSkolem (Skolem v) = Just v
    fromSkolem _ = Nothing

type MyAtom = FOL Predicate (Term Function V)
type MyFormula = Formula MyAtom

-- Example.

test04 :: Test
test04 = TestCase $ assertEqual "skolemize 1 (p. 150)" expected input
    where input = runSkolem (skolemize fm) :: Formula (FOL Predicate (Term Function V))
          fm :: Formula (FOL Predicate (Term Function V))
          fm = exists "y" (pApp ("<") [vt "x", vt "y"] .=>.
                           for_all "u" (exists "v" (pApp ("<") [fApp "*" [vt "x", vt "u"],  fApp "*" [vt "y", vt "v"]])))
          expected = ((.~.)(pApp ("<") [vt "x",fApp (Skolem "y") [vt "x"]])) .|.
                     (pApp ("<") [fApp "*" [vt "x",vt "u"],fApp "*" [fApp (Skolem "y") [vt "x"],fApp (Skolem "v") [vt "u",vt "x"]]])

test05 :: Test
test05 = TestCase $ assertEqual "skolemize 2 (p. 150)" expected input
    where p = "P"
          q = "Q"
          input = runSkolem (skolemize fm) :: Formula (FOL Predicate (Term Function V))
          fm :: Formula (FOL Predicate (Term Function V))
          fm = for_all "x" ((pApp p [vt "x"]) .=>.
                            (exists "y" (exists "z" ((pApp q [vt "y"]) .|.
                                                     ((.~.)(exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))))))))
          expected = ((.~.)(pApp p [vt "x"])) .|.
                     ((pApp q [fApp (Skolem "y") []]) .|.
                      (((.~.)(pApp p [vt "z"])) .|.
                       ((.~.)(pApp q [vt "z"]))))

tests :: Test
tests = TestList [test01, test02, test03, test04, test05]
