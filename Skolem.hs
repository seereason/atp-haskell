{-# LANGUAGE FlexibleContexts, GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
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
simplify1 :: (atom ~ FOL predicate formula v, FirstOrderFormula (Formula atom) atom v, Ord predicate, Ord formula) =>
             Formula atom -> Formula atom
simplify1 fm =
    foldFirstOrder qu co (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) fm
    where
      qu _ x p = if member x (fv p) then fm else p
      -- If psimplify1 sees a negation it looks at its argument, so here we
      -- make sure that argument isn't a quantifier which would cause an error.
      co ((:~:) p) = foldFirstOrder (\_ _ _ -> fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) p
      co _ = psimplify1 fm

simplify :: (atom ~ FOL predicate formula v, FirstOrderFormula (Formula atom) atom v, Ord predicate, Ord formula, Ord v) =>
            Formula atom -> Formula atom
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

-- | Use a predicate to combine some terms into a formula.
pApp :: predicate -> [Term function v] -> Formula (FOL predicate function v)
pApp p args = Atom $ R p args

test01 :: Test
test01 = TestCase $ assertEqual ("simplify (p. 140) " ++ prettyShow fm) expected input
    where input = prettyShow (simplify fm)
          expected = prettyShow ((for_all "x" (pApp "P" [vt "x"])) .=>. (pApp "Q" []) :: Formula (FOL Predicate FName V))
          fm :: Formula (FOL Predicate FName V)
          fm = (for_all "x" (for_all "y" (pApp "P" [vt "x"] .|. (pApp "P" [vt "y"] .&. false)))) .=>. exists "z" (pApp "Q" [])

-- | Negation normal form.
nnf :: forall a. Formula a -> Formula a
nnf fm =
  case fm of
    And p q -> And (nnf p) (nnf q)
    Or p q -> Or (nnf p) (nnf q)
    Imp p q -> Or (nnf (Not p)) (nnf q)
    Iff p q -> Or (And (nnf p) (nnf q)) (And (nnf (Not p)) (nnf (Not q)))
    Not (Not p) -> nnf p
    Not (And p q) -> Or (nnf (Not p)) (nnf (Not q))
    Not (Or p q) -> And (nnf (Not p)) (nnf (Not q))
    Not (Imp p q) -> And (nnf p) (nnf (Not q))
    Not (Iff p q) -> Or (And (nnf p) (nnf (Not q))) (And (nnf (Not p)) (nnf q))
    Forall x p -> Forall x (nnf p)
    Exists x p -> Exists x (nnf p)
    Not (Forall x p) -> Exists x (nnf (Not p))
    Not (Exists x p) -> Forall x (nnf (Not p))
    _ -> fm

-- Example of NNF function in action.
test02 :: Test
test02 = TestCase $ assertEqual "nnf (p. 140)" expected input
    where p = "P"
          q = "Q"
          input = nnf fm
          expected = exists "x" ((.~.)(pApp p [vt "x"])) .|.
                     ((exists "y" (pApp q [vt "y"]) .&. exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))) .|.
                      (for_all "y" ((.~.)(pApp q [vt "y"])) .&.
                       for_all "z" (((.~.)(pApp p [vt "z"])) .|. ((.~.)(pApp q [vt "z"])))) :: Formula (FOL Predicate FName V))
          fm :: Ord function => Formula (FOL Predicate function V)
          fm = (for_all "x" (pApp p [vt "x"])) .=>. ((exists "y" (pApp q [vt "y"])) .<=>. exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"]))

-- | Prenex normal form.
pullquants :: forall atom predicate function v.
              (atom ~ FOL predicate function v,
               FirstOrderFormula (Formula atom) atom v,
               Ord function
              ) => Formula atom -> Formula atom
pullquants fm =
    foldFirstOrder (\_ _ _ -> fm) pullQuantsCombine (\_ -> fm) (\_ -> fm) fm
    where
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

pullq :: (atom ~ FOL predicate function v,
         FirstOrderFormula (Formula atom) atom v, Ord function) =>
         (Bool, Bool)
      -> Formula atom
      -> (v -> Formula atom -> Formula atom)
      -> (Formula atom -> Formula atom -> Formula atom)
      -> v
      -> v
      -> Formula atom
      -> Formula atom
      -> Formula atom
pullq (l,r) fm qu op x y p q =
  let z = variant x (fv fm) in
  let p' = if l then subst (Map.singleton x (vt z)) p else p
      q' = if r then subst (Map.singleton y (vt z)) q else q in
  qu z (pullquants (op p' q'))

prenex :: (atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v, Ord function) => Formula atom -> Formula atom
prenex fm =
    foldFirstOrder qu co (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co (BinOp l (:&:) r) = pullquants (prenex l .&. prenex r)
      co (BinOp l (:|:) r) = pullquants (prenex l .|. prenex r)
      co _ = fm

pnf :: (atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v, Ord predicate, Ord function) => Formula atom -> Formula atom
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
                                    ((.~.)(pApp q [vt "z"])))))) :: Formula (FOL Predicate Function V)
          fm :: Ord function => Formula (FOL Predicate function V)
          fm = (for_all "x" (pApp p [vt "x"]) .|. (pApp r [vt "y"])) .=>.
               exists "y" (exists "z" ((pApp q [vt "y"]) .|. ((.~.)(exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"])))))


-- | Get the functions in a term and formula.
functions :: (f ~ String) => (atom -> Set (f, Int)) -> Formula atom -> Set (f, Int)
functions fa fm =
    case fm of
      Atom a -> fa a
      Not p -> functions fa p
      And p q -> functions fa p <> functions fa q
      Or p q -> functions fa p <> functions fa q
      Imp p q -> functions fa p <> functions fa q
      Iff p q -> functions fa p <> functions fa q
      Forall _ p -> functions fa p
      Exists _ p -> functions fa p
      F -> mempty
      T -> mempty

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
class Skolem function var where
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
skolem :: (Monad m, Ord function, Skolem function v, atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v) =>
          Formula atom -> SkolemT m (Formula atom)
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

skolem2 :: (Monad m, Ord function, Skolem function v, atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v) =>
           (Formula atom -> Formula atom -> Formula atom) -> Formula atom -> Formula atom -> SkolemT m (Formula atom)
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- | Overall Skolemization function.
askolemize :: (Monad m, Skolem function v, atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v, Ord predicate, Ord function) =>
              Formula atom -> SkolemT m (Formula atom)
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.
specialize :: Formula atom -> Formula atom
specialize f =
    case f of
      Forall _x p -> specialize p
      _ -> f

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of PropositionalFormula.
skolemize :: (Monad m, Skolem function v, atom ~ FOL predicate function v, FirstOrderFormula (Formula atom) atom v, Ord predicate, Ord function) =>
             Formula atom
          -> SkolemT m (Formula atom)
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

-- Example.

test04 :: Test
test04 = TestCase $ assertEqual "skolemize 1 (p. 150)" expected input
    where input = runSkolem (skolemize fm) :: Formula (FOL Predicate Function V)
          fm :: Formula (FOL Predicate Function V)
          fm = exists "y" (pApp ("<") [vt "x", vt "y"] .=>.
                           for_all "u" (exists "v" (pApp ("<") [fApp "*" [vt "x", vt "u"],  fApp "*" [vt "y", vt "v"]])))
          expected = ((.~.)(pApp ("<") [vt "x",fApp (Skolem "y") [vt "x"]])) .|.
                     (pApp ("<") [fApp "*" [vt "x",vt "u"],fApp "*" [fApp (Skolem "y") [vt "x"],fApp (Skolem "v") [vt "u",vt "x"]]])

test05 :: Test
test05 = TestCase $ assertEqual "skolemize 2 (p. 150)" expected input
    where p = "P"
          q = "Q"
          input = runSkolem (skolemize fm) :: Formula (FOL Predicate Function V)
          fm :: Formula (FOL Predicate Function V)
          fm = for_all "x" ((pApp p [vt "x"]) .=>.
                            (exists "y" (exists "z" ((pApp q [vt "y"]) .|.
                                                     ((.~.)(exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))))))))
          expected = ((.~.)(pApp p [vt "x"])) .|.
                     ((pApp q [fApp (Skolem "y") []]) .|.
                      (((.~.)(pApp p [vt "z"])) .|.
                       ((.~.)(pApp q [vt "z"]))))

tests :: Test
tests = TestList [test01, test02, test03, test04, test05]
