-- | Unification for first order terms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Unif
    ( Unify(unify)
    , unify_terms
    , unify_literals
    , unify_atoms
    , unify_atoms_eq
    , solve
    , fullunify
    , unify_and_apply
    , testUnif
    ) where

import Apply (HasApply(TermOf), JustApply, zipApplys)
import Control.Monad.State -- (evalStateT, runStateT, State, StateT, get)
import Data.Bool (bool)
import Data.List as List (map)
import Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq, viewl, ViewL(EmptyL, (:<)))
import Equate (HasEquate, zipEquates)
import FOL (tsubst)
import Formulas (IsFormula(AtomOf))
import Lib (Failing(Success, Failure))
import Lit (IsLiteral, zipLiterals')
import Skolem (SkAtom, SkTerm)
import Term (IsTerm(..), V)
import Test.HUnit hiding (State)

-- | Main unification procedure.
class Unify a v term where
    unify :: a -> a -> StateT (Map v term) Failing ()
    -- ^ Unify the two elements of a pair, collecting variable
    -- assignments in the state.

instance Unify a v term => Unify [a] v term where
    unify [] [] = return ()
    unify (x : xs) (y : ys) = unify x y >> unify xs ys
    unify _ _ = fail "unify - list length mismatch"

instance Unify a v term => Unify (Seq a) v term where
    unify xs ys =
        case (viewl xs, viewl ys) of
          (EmptyL, EmptyL) -> return ()
          (x :< xs', y :< ys') -> unify x y >> unify xs' ys'
          _ -> fail "unify - Seq list length mismatch"

unify_terms :: (IsTerm term, v ~ TVarOf term) => [(term,term)] -> StateT (Map v term) Failing ()
unify_terms = mapM_ (uncurry unify_term_pair)

unify_term_pair :: forall term v f. (IsTerm term, v ~ TVarOf term, f ~ FunOf term) =>
                   term -> term -> StateT (Map v term) Failing ()
unify_term_pair a b =
    foldTerm (vr b) (\ f fargs -> foldTerm (vr a) (fn f fargs) b) a
    where
      vr :: term -> v -> StateT (Map v term) Failing ()
      vr t x =
          (Map.lookup x <$> get) >>=
          maybe (istriv x t >>= bool (modify (Map.insert x t)) (return ()))
                (\y -> unify_term_pair y t)
      fn :: f -> [term] -> f -> [term] -> StateT (Map v term) Failing ()
      fn f fargs g gargs =
          if f == g && length fargs == length gargs
          then mapM_ (uncurry unify_term_pair) (zip fargs gargs)
          else fail "impossible unification"

istriv :: forall term v. (IsTerm term, v ~ TVarOf term) =>
          v -> term -> StateT (Map v term) Failing Bool
istriv x t =
    foldTerm vr fn t
    where
      -- vr :: v -> StateT (Map v term) Failing Bool
      vr y | x == y = return True
      vr y = (Map.lookup y <$> get) >>= maybe (return False) (istriv x)
      -- fn :: f -> [term] -> StateT (Map v term) Failing Bool
      fn _ args = mapM (istriv x) args >>= bool (return False) (fail "cyclic") . or

-- | Solve to obtain a single instantiation.
solve :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term) =>
         Map v term -> Map v term
solve env =
    if env' == env then env else solve env'
    where env' = Map.map (tsubst env) env

-- | Unification reaching a final solved form (often this isn't needed).
fullunify :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term) =>
             [(term,term)] -> Failing (Map v term)
fullunify eqs = solve <$> execStateT (unify_terms eqs) Map.empty

-- | Examples.
unify_and_apply :: (IsTerm term, v ~ TVarOf term, f ~ FunOf term) =>
                   [(term, term)] -> Failing [(term, term)]
unify_and_apply eqs =
    fullunify eqs >>= \i -> return $ List.map (\ (t1, t2) -> (tsubst i t1, tsubst i t2)) eqs

-- | Unify literals
unify_literals :: (IsLiteral lit, HasApply atom, Unify atom v term,
                   atom ~ AtomOf lit, term ~ TermOf atom, v ~ TVarOf term) =>
                  lit -> lit -> StateT (Map v term) Failing ()
unify_literals f1 f2 =
    fromMaybe (fail "Can't unify literals") (zipLiterals' ho ne tf at f1 f2)
    where
      ho _ _ = Nothing
      ne p q = Just $ unify_literals p q
      tf p q = if p == q then Just (unify_terms []) else Nothing
      at a1 a2 = Just (unify a1 a2)

unify_atoms :: (JustApply atom, term ~ TermOf atom, v ~ TVarOf term) =>
               (atom, atom) -> StateT (Map v term) Failing ()
unify_atoms (a1, a2) =
    maybe (fail "unify_atoms") id (zipApplys (\_ tpairs -> Just (unify_terms tpairs)) a1 a2)

unify_atoms_eq :: (HasEquate atom, term ~ TermOf atom, v ~ TVarOf term) =>
                  atom -> atom -> StateT (Map v term) Failing ()
unify_atoms_eq a1 a2 =
    maybe (fail "unify_atoms") id (zipEquates (\l1 r1 l2 r2 -> Just (unify_terms [(l1, l2), (r1, r2)]))
                                              (\_ tpairs -> Just (unify_terms tpairs))
                                              a1 a2)

--unify_and_apply' :: (v ~ TVarOf term, f ~ FunOf term, IsTerm term) => [(term, term)] -> Failing [(term, term)]
--unify_and_apply' eqs =
--    mapM app eqs
--        where
--          app (t1, t2) = fullunify eqs >>= \i -> return $ (tsubst i t1, tsubst i t2)

instance Unify SkAtom V SkTerm where
    unify = unify_atoms_eq

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
