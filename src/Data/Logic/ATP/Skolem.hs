-- | Prenex and Skolem normal forms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Logic.ATP.Skolem
    (
    -- * Class of Skolem functions
      HasSkolem(SVarOf, toSkolem, foldSkolem, variantSkolem)
    , showSkolem
    , prettySkolem
    -- * Skolem monad
    , SkolemM
    , runSkolem
    , SkolemT
    , runSkolemT
    -- * Skolemization procedure
    , simplify
    , nnf
    , pnf
    , skolems
    , askolemize
    , skolemize
    , specialize
    -- * Normalization
    , simpdnf'
    , simpcnf'
    -- * Instances
    , Function(Fn, Skolem)
    , Formula, SkTerm, SkAtom
    -- * Tests
    , testSkolem
    ) where

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (runStateT, StateT, get, modify)
import Data.Data (Data)
import Data.List as List (map)
import Data.Logic.ATP.Apply (functions, HasApply(TermOf, PredOf), pApp, Predicate)
import Data.Logic.ATP.Equate (FOL)
import Data.Logic.ATP.FOL (fv, IsFirstOrder, subst)
import Data.Logic.ATP.Formulas (IsFormula(AtomOf), false, true, atomic)
import Data.Logic.ATP.Lib (setAny, distrib)
import Data.Logic.ATP.Lit ((.~.), negate)
import Data.Logic.ATP.Pretty (brackets, Doc, Pretty(pPrint), prettyShow, text)
import Data.Logic.ATP.Prop ((.&.), (.|.), (.=>.), (.<=>.), BinOp((:&:), (:|:), (:=>:), (:<=>:)),
                            convertToPropositional, foldPropositional', JustPropositional, PFormula, psimplify1, trivial)
import Data.Logic.ATP.Quantified (exists, for_all, IsQuantified(VarOf, foldQuantified),
                                  QFormula, quant, Quant((:?:), (:!:)))
import Data.Logic.ATP.Term (fApp, IsFunction, IsTerm(TVarOf, FunOf), IsVariable, Term, V, variant, vt)
import Data.Map.Strict as Map (singleton)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, insert, isProperSubsetOf, map, member, notMember, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Prelude hiding (negate)
import Test.HUnit

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
class (IsFunction function, IsVariable (SVarOf function)) => HasSkolem function where
    type SVarOf function
    toSkolem :: SVarOf function -> Int -> function
    -- ^ Create a skolem function with a variant number that differs
    -- from all the members of the set.
    foldSkolem :: (function -> r) -> (SVarOf function -> Int -> r) -> function -> r
    variantSkolem :: function -> Set function -> function
    -- ^ Return a function based on f but different from any set
    -- element.  The result may be f itself if f is not a member of
    -- the set.

-- fromSkolem :: HasSkolem function v => function -> Maybe v
-- fromSkolem = foldSkolem (const Nothing) Just

showSkolem :: (HasSkolem function, IsVariable (SVarOf function)) => function -> String
showSkolem = foldSkolem (show . prettyShow) (\v n -> "(toSkolem " ++ show v ++ " " ++ show n ++ ")")

prettySkolem :: HasSkolem function => (function -> Doc) -> function -> Doc
prettySkolem prettyFunction =
    foldSkolem prettyFunction (\v n -> text "sK" <> brackets (pPrint v <> if n == 1 then mempty else (text "." <> pPrint (show n))))

-- | State monad for generating Skolem functions and constants.
type SkolemT m function = StateT (SkolemState function) m
type SkolemM function = StateT (SkolemState function) Identity

-- | The state associated with the Skolem monad.
data SkolemState function
    = SkolemState
      { skolemSet :: Set function
        -- ^ The set of allocated skolem functions
      , univQuant :: [String]
        -- ^ The variables which are universally quantified in the
        -- current scope, in the order they were encountered.  During
        -- Skolemization these are the parameters passed to the Skolem
        -- function.
      }

-- | Run a computation in a stacked invocation of the Skolem monad.
runSkolemT :: (Monad m, IsFunction function) => SkolemT m function a -> m a
runSkolemT action = (runStateT action) newSkolemState >>= return . fst
    where
      newSkolemState :: IsFunction function => SkolemState function
      newSkolemState
          = SkolemState
            { skolemSet = mempty
            , univQuant = []
            }

-- | Run a pure computation in the Skolem monad.
runSkolem :: IsFunction function => SkolemT Identity function a -> a
runSkolem = runIdentity . runSkolemT

-- -------------------------------------------------------------------------
-- Simplification, normal forms, and the skolemization procedure
-- -------------------------------------------------------------------------

-- | Routine simplification. Like "psimplify" but with quantifier clauses.
simplify :: IsFirstOrder formula => formula -> formula
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

simplify1 :: IsFirstOrder formula => formula -> formula
simplify1 fm =
    foldQuantified qu (\_ _ _ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) (\_ -> psimplify1 fm) fm
    where
      qu _ x p = if member x (fv p) then fm else p

-- Example.
test01 :: Test
test01 = TestCase $ assertEqual ("simplify (p. 140) " ++ prettyShow fm) expected input
    where input = prettyShow (simplify fm)
          expected = prettyShow ((for_all "x" (pApp "P" [vt "x"])) .=>. (pApp "Q" []) :: Formula)
          fm :: Formula
          fm = (for_all "x" (for_all "y" (pApp "P" [vt "x"] .|. (pApp "P" [vt "y"] .&. false)))) .=>. exists "z" (pApp "Q" [])

-- | Negation normal form for first order formulas
nnf :: IsFirstOrder formula => formula -> formula
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

-- Example of NNF function in action.
test02 :: Test
test02 = TestCase $ assertEqual "nnf (p. 140)" expected input
    where p = "P"
          q = "Q"
          input = nnf fm
          expected = exists "x" ((.~.)(pApp p [vt "x"])) .|.
                     ((exists "y" (pApp q [vt "y"]) .&. exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))) .|.
                      (for_all "y" ((.~.)(pApp q [vt "y"])) .&.
                       for_all "z" (((.~.)(pApp p [vt "z"])) .|. ((.~.)(pApp q [vt "z"])))) :: Formula)
          fm :: Formula
          fm = (for_all "x" (pApp p [vt "x"])) .=>. ((exists "y" (pApp q [vt "y"])) .<=>. exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"]))

-- | Prenex normal form.
pnf :: IsFirstOrder formula => formula -> formula
pnf = prenex . nnf . simplify

prenex :: IsFirstOrder formula => formula -> formula
prenex fm =
    foldQuantified qu co (\ _ -> fm) (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co l (:&:) r = pullquants (prenex l .&. prenex r)
      co l (:|:) r = pullquants (prenex l .|. prenex r)
      co _ _ _ = fm

pullquants :: IsFirstOrder formula => formula -> formula
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

pullq :: (IsFirstOrder formula, v ~ VarOf formula) =>
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
                                    ((.~.)(pApp q [vt "z"])))))) :: Formula
          fm :: Formula
          fm = (for_all "x" (pApp p [vt "x"]) .|. (pApp r [vt "y"])) .=>.
               exists "y" (exists "z" ((pApp q [vt "y"]) .|. ((.~.)(exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"])))))

-- | Extract the skolem functions from a formula.
skolems :: (IsFormula formula, HasSkolem function, HasApply atom, Ord function,
            atom ~ AtomOf formula,
            term ~ TermOf atom,
            function ~ FunOf term {-,
            v ~ TVarOf term,
            v ~ SVarOf function-}) => formula -> Set function
skolems = Set.filter (foldSkolem (const False) (\_ _ -> True)) . Set.map fst . functions

-- | Core Skolemization function.
--
-- Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the SkolemT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (IsFirstOrder formula, HasSkolem function, Monad m,
           atom ~ AtomOf formula,
           term ~ TermOf atom,
           function ~ FunOf term,
           VarOf formula ~ SVarOf function {-,
           predicate ~ PredOf atom-}) =>
          formula -> SkolemT m function formula
skolem fm =
    foldQuantified qu co ne tf (return . atomic) fm
    where
      qu (:?:) y p =
          do sk <- newSkolem y
             let xs = fv fm
             let fx = fApp sk (List.map vt (Set.toAscList xs))
             skolem (subst (Map.singleton y fx) p)
      qu (:!:) x p = skolem p >>= return . for_all x
      co l (:&:) r = skolem2 (.&.) l r
      co l (:|:) r = skolem2 (.|.) l r
      co _ _ _ = return fm
      ne _ = return fm
      tf True = return true
      tf False = return false

newSkolem :: (Monad m, HasSkolem function, v ~ SVarOf function) => v -> SkolemT m function function
newSkolem v = do
  f <- variantSkolem (toSkolem v 1) <$> skolemSet <$> get
  modify (\s -> s {skolemSet = Set.insert f (skolemSet s)})
  return f

skolem2 :: (IsFirstOrder formula, HasSkolem function, Monad m,
            atom ~ AtomOf formula,
            term ~ TermOf atom,
            function ~ FunOf term,
            VarOf formula ~ SVarOf function) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT m function formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- | Overall Skolemization function.
askolemize :: (IsFirstOrder formula, HasSkolem function, Monad m,
               atom ~ AtomOf formula,
               term ~ TermOf atom,
               function ~ FunOf term,
               VarOf formula ~ SVarOf function) =>
              formula -> SkolemT m function formula
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.  For this reason we can safely convert to any
-- instance of IsPropositional.
specialize :: (IsQuantified fof, JustPropositional pf) => (AtomOf fof -> AtomOf pf) -> fof -> pf
specialize ca fm =
    convertToPropositional (error "specialize failure") ca (specialize' fm)
    where
      specialize' p = foldQuantified qu (\_ _ _ -> p) (\_ -> p) (\_ -> p) (\_ -> p) p
      qu (:!:) _ p = specialize' p
      qu _ _ _ = fm

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of IsPropositional.
skolemize :: (IsFirstOrder formula, JustPropositional pf, HasSkolem function, Monad m,
              atom ~ AtomOf formula,
              term ~ TermOf atom,
              function ~ FunOf term,
              VarOf formula ~ SVarOf function) =>
             (AtomOf formula -> AtomOf pf) -> formula -> StateT (SkolemState function) m pf
skolemize ca fm = (specialize ca . pnf) <$> askolemize fm

-- | A function type that is an instance of HasSkolem
data Function
    = Fn String
    | Skolem V Int
    deriving (Eq, Ord, Data, Typeable, Read)

instance IsFunction Function

instance IsString Function where
    fromString = Fn

instance Show Function where
    show = showSkolem

instance Pretty Function where
    pPrint = prettySkolem (\(Fn s) -> text s)

instance HasSkolem Function where
    type SVarOf Function = V
    toSkolem = Skolem
    foldSkolem _ sk (Skolem v n) = sk v n
    foldSkolem other _ f = other f
    variantSkolem f fns | Set.notMember f fns = f
    variantSkolem (Fn s) fns = variantSkolem (fromString (s ++ "'")) fns
    variantSkolem (Skolem v n) fns = variantSkolem (Skolem v (succ n)) fns

-- | A first order logic formula type with an equality predicate and skolem functions.
type Formula = QFormula V SkAtom
type SkAtom = FOL Predicate SkTerm
type SkTerm = Term Function V

instance IsFirstOrder Formula

test04 :: Test
test04 = TestCase $ assertEqual "skolemize 1 (p. 150)" expected input
    where input = runSkolem (skolemize id fm) :: PFormula SkAtom
          fm :: Formula
          fm = exists "y" (pApp ("<") [vt "x", vt "y"] .=>.
                           for_all "u" (exists "v" (pApp ("<") [fApp "*" [vt "x", vt "u"],  fApp "*" [vt "y", vt "v"]])))
          expected = ((.~.)(pApp ("<") [vt "x",fApp (Skolem "y" 1) [vt "x"]])) .|.
                     (pApp ("<") [fApp "*" [vt "x",vt "u"],fApp "*" [fApp (Skolem "y" 1) [vt "x"],fApp (Skolem "v" 1) [vt "u",vt "x"]]])

test05 :: Test
test05 = TestCase $ assertEqual "skolemize 2 (p. 150)" expected input
    where p = "P"
          q = "Q"
          input = runSkolem (skolemize id fm) :: PFormula SkAtom
          fm :: Formula
          fm = for_all "x" ((pApp p [vt "x"]) .=>.
                            (exists "y" (exists "z" ((pApp q [vt "y"]) .|.
                                                     ((.~.)(exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))))))))
          expected = ((.~.)(pApp p [vt "x"])) .|.
                     ((pApp q [fApp (Skolem "y" 1) []]) .|.
                      (((.~.)(pApp p [vt "z"])) .|.
                       ((.~.)(pApp q [vt "z"]))))

-- | Versions of the normal form functions that leave quantifiers in place.
simpdnf' :: (IsFirstOrder fof, Ord fof,
             atom ~ AtomOf fof, term ~ TermOf atom, function ~ FunOf term,
             v ~ VarOf fof, v ~ TVarOf term) =>
            fof -> Set (Set fof)
simpdnf' fm =
    foldQuantified (\_ _ _ -> go) (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf' (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs

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

testSkolem :: Test
testSkolem = TestLabel "Skolem" (TestList [test01, test02, test03, test04, test05])
