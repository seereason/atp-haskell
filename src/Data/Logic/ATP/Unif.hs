-- | Unification for first order terms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.Unif
    ( Unify(unify', UTermOf)
    , unify
    , unify_terms
    , unify_literals
    , unify_atoms
    , unify_atoms_eq
    , solve
    , fullunify
    , unify_and_apply
    , testUnif
    ) where

import Control.Monad.State -- (evalStateT, runStateT, State, StateT, get)
import Data.Bool (bool)
import Data.List as List (map)
import Data.Logic.ATP.Apply (HasApply(TermOf, PredOf), JustApply, zipApplys)
import Data.Logic.ATP.Equate (HasEquate, zipEquates)
import Data.Logic.ATP.FOL (tsubst)
import Data.Logic.ATP.Formulas (IsFormula(AtomOf))
import Data.Logic.ATP.Lib (Failing(Success, Failure))
import Data.Logic.ATP.Lit (IsLiteral, JustLiteral, zipLiterals')
import Data.Logic.ATP.Skolem (SkAtom, SkTerm)
import Data.Logic.ATP.Term (IsTerm(..), IsVariable)
import Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
-- import Data.Sequence (Seq, viewl, ViewL(EmptyL, (:<)))
import Test.HUnit hiding (State)

-- | Main unification procedure.  The result of unification is a
-- mapping of variables to terms, so although we can unify two
-- dissimilar types, they must at least have the same term type (which
-- means the variable type will also match.)  The result of unifying
-- the two arguments is added to the state, while failure is signalled
-- in the Failing monad.
--
-- One might think that Unify should take two type parameters, the
-- types of two values to be unified, but there are instances where a
-- single type contains both - for example, in template-haskell we
-- want to unify a and b in a predicate such as this: @(AppT (AppT
-- EqualityT a) b)@.
class (Monad m, IsTerm (UTermOf a), IsVariable (TVarOf (UTermOf a))) => Unify m a where
    type UTermOf a
    unify' :: a -> StateT (Map (TVarOf (UTermOf a)) (UTermOf a)) m ()

unify :: (Unify m a, Monad m) => a -> Map (TVarOf (UTermOf a)) (UTermOf a) -> m (Map (TVarOf (UTermOf a)) (UTermOf a))
unify a mp0 = execStateT (unify' a) mp0

unify_terms :: (IsTerm term, v ~ TVarOf term, Monad m) =>
               [(term,term)] -> StateT (Map v term) m ()
unify_terms = mapM_ (uncurry unify_term_pair)

unify_term_pair :: forall term v f m.
                   (IsTerm term, v ~ TVarOf term, f ~ FunOf term, Monad m) =>
                   term -> term -> StateT (Map v term) m ()
unify_term_pair a b =
    foldTerm (vr b) (\ f fargs -> foldTerm (vr a) (fn f fargs) b) a
    where
      vr :: term -> v -> StateT (Map v term) m ()
      vr t x =
          (Map.lookup x <$> get) >>=
          maybe (istriv x t >>= bool (modify (Map.insert x t)) (return ()))
                (\y -> unify_term_pair y t)
      fn :: f -> [term] -> f -> [term] -> StateT (Map v term) m ()
      fn f fargs g gargs =
          if f == g && length fargs == length gargs
          then mapM_ (uncurry unify_term_pair) (zip fargs gargs)
          else fail "impossible unification"

istriv :: forall term v f m. (IsTerm term, v ~ TVarOf term, f ~ FunOf term, Monad m) =>
          v -> term -> StateT (Map v term) m Bool
istriv x t =
    foldTerm vr fn t
    where
      vr :: v -> StateT (Map v term) m Bool
      vr y | x == y = return True
      vr y = (Map.lookup y <$> get) >>= \(mt :: Maybe term) -> maybe (return False) (istriv x) mt
      fn :: f -> [term] -> StateT (Map v term) m Bool
      fn _ args = mapM (istriv x) args >>= bool (return False) (fail "cyclic") . or

-- | Solve to obtain a single instantiation.
solve :: (IsTerm term, v ~ TVarOf term) =>
         Map v term -> Map v term
solve env =
    if env' == env then env else solve env'
    where env' = Map.map (tsubst env) env

-- | Unification reaching a final solved form (often this isn't needed).
fullunify :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term, Monad m) =>
             [(term,term)] -> m (Map v term)
fullunify eqs = solve <$> execStateT (unify_terms eqs) Map.empty

-- | Examples.
unify_and_apply :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term, Monad m) =>
                   [(term, term)] -> m [(term, term)]
unify_and_apply eqs =
    fullunify eqs >>= \i -> return $ List.map (\ (t1, t2) -> (tsubst i t1, tsubst i t2)) eqs

-- | Unify literals, perhaps of different types, but sharing term and
-- variable type.  Note that only one needs to be 'JustLiteral', if
-- the unification succeeds the other must have been too, if it fails,
-- who cares.
unify_literals :: forall lit1 lit2 atom1 atom2 v term m.
                  (IsLiteral lit1, HasApply atom1, atom1 ~ AtomOf lit1, term ~ TermOf atom1,
                   JustLiteral lit2, HasApply atom2, atom2 ~ AtomOf lit2, term ~ TermOf atom2,
                   Unify m (atom1, atom2), term ~ UTermOf (atom1, atom2), v ~ TVarOf term) =>
                  lit1 -> lit2 -> StateT (Map v term) m ()
unify_literals f1 f2 =
    fromMaybe (fail "Can't unify literals") (zipLiterals' ho ne tf at f1 f2)
    where
      ho _ _ = Nothing
      ne p q = Just $ unify_literals p q
      -- tf :: Bool -> Bool -> Maybe (StateT (Map v term) m ())
      tf p q = if p == q then Just (unify_terms ([] :: [(term, term)])) else Nothing
      at a1 a2 = Just (unify' (a1, a2))

unify_atoms :: (JustApply atom1, term ~ TermOf atom1,
                JustApply atom2, term ~ TermOf atom2,
                v ~ TVarOf term, PredOf atom1 ~ PredOf atom2, Monad m) =>
               (atom1, atom2) -> StateT (Map v term) m ()
unify_atoms (a1, a2) =
    maybe (fail "unify_atoms") id (zipApplys (\_ tpairs -> Just (unify_terms tpairs)) a1 a2)

unify_atoms_eq :: (HasEquate atom1, term ~ TermOf atom1,
                   HasEquate atom2, term ~ TermOf atom2,
                   PredOf atom1 ~ PredOf atom2, v ~ TVarOf term, Monad m) =>
                  atom1 -> atom2 -> StateT (Map v term) m ()
unify_atoms_eq a1 a2 =
    maybe (fail "unify_atoms") id (zipEquates (\l1 r1 l2 r2 -> Just (unify_terms [(l1, l2), (r1, r2)]))
                                              (\_ tpairs -> Just (unify_terms tpairs))
                                              a1 a2)

--unify_and_apply' :: (v ~ TVarOf term, f ~ FunOf term, IsTerm term, Monad m) => [(term, term)] -> m [(term, term)]
--unify_and_apply' eqs =
--    mapM app eqs
--        where
--          app (t1, t2) = fullunify eqs >>= \i -> return $ (tsubst i t1, tsubst i t2)

instance Monad m => Unify m (SkAtom, SkAtom) where
    type UTermOf (SkAtom, SkAtom) = TermOf SkAtom
    unify' = uncurry unify_atoms_eq

test01, test02, test03, test04 :: Test
test01 = TestCase (assertEqual "Unify test 1"
                     (Success [(f [f [z],g [y]],
                                f [f [z],g [y]])]) -- expected
                     (unify_and_apply [(f [x, g [y]], f [f [z], w])]))
    where
      [f, g] = [fApp "f", fApp "g"]
      [w, x, y, z] = [vt "w", vt "x", vt "y", vt "z"] :: [SkTerm]
test02 = TestCase (assertEqual "Unify test 2"
                     (Success [(f [y,y],
                                f [y,y])]) -- expected
                     (unify_and_apply [(f [x, y], f [y, x])]))
    where
      [f] = [fApp "f"]
      [x, y] = [vt "x", vt "y"] :: [SkTerm]
test03 = TestCase (assertEqual "Unify test 3"
                     (Failure ["cyclic"]) -- expected
                     (unify_and_apply [(f [x, g [y]], f [y, x])]))
    where
      [f, g] = [fApp "f", fApp "g"]
      [x, y] = [vt "x", vt "y"] :: [SkTerm]
test04 = TestCase (assertEqual "Unify test 4"
                     (Success [(f [f [f [x_3,x_3],f [x_3,x_3]], f [f [x_3,x_3],f [x_3,x_3]]],
                                f [f [f [x_3,x_3],f [x_3,x_3]], f [f [x_3,x_3],f [x_3,x_3]]]),
                               (f [f [x_3,x_3],f [x_3,x_3]],
                                f [f [x_3,x_3],f [x_3,x_3]]),
                               (f [x_3,x_3],
                                f [x_3,x_3])]) -- expected
                     (unify_and_apply [(x_0, f [x_1, x_1]),
                                       (x_1, f [x_2, x_2]),
                                       (x_2, f [x_3, x_3])]))

    where
      f = fApp "f"
      [x_0, x_1, x_2, x_3] = [vt "x0", vt "x1", vt "x2", vt "x3"] :: [SkTerm]
{-

START_INTERACTIVE;;
unify_and_apply [<<|f(x,g(y))|>>,<<|f(f(z),w)|>>];;

unify_and_apply [<<|f(x,y)|>>,<<|f(y,x)|>>];;

(****  unify_and_apply [<<|f(x,g(y))|>>,<<|f(y,x)|>>];; *****)

unify_and_apply [<<|x_0|>>,<<|f(x_1,x_1)|>>;
                 <<|x_1|>>,<<|f(x_2,x_2)|>>;
                 <<|x_2|>>,<<|f(x_3,x_3)|>>];;
END_INTERACTIVE;;
-}

testUnif :: Test
testUnif = TestLabel "Unif" (TestList [test01, test02, test03, test04])
