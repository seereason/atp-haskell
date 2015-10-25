-- | Unification for first order terms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# OPTIONS -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Unif
    ( unify
    , solve
    , fullunify
    , unify_and_apply
#ifndef NOTESTS
    , testUnif
#endif
    ) where

import Data.Bool (bool)
import Data.List as List (map)
import Data.Map as Map
import FOL (IsTerm(..), tsubst)
import Lib (Failing)
#ifndef NOTESTS
import Lib (Failing(Success, Failure))
import Skolem (MyTerm)
import Test.HUnit
#endif

-- | Main unification procedure.  Using the Monad instance of Failing here and in istriv.
unify :: IsTerm term v f => Map v term -> [(term,term)] -> Failing (Map v term)
unify env [] = return env
unify env ((a,b):oth) =
    foldTerm (vr b) (\ f fargs -> foldTerm (vr a) (fn f fargs) b) a
    where
      vr t x =
          maybe (istriv env x t >>= bool (unify (Map.insert x t env) oth) (unify env oth))
                (\y -> unify env ((y, t) : oth)) -- x is bound to y, so unify y with t
                (Map.lookup x env)
      fn f fargs g gargs =
          if f == g && length fargs == length gargs
          then unify env (zip fargs gargs ++ oth)
          else fail "impossible unification"

istriv :: IsTerm term v f => Map v term -> v -> term -> Failing Bool
istriv env x t =
    foldTerm vr fn t
    where
      vr y | x == y = return True
      vr y = maybe (return False) (istriv env x) (Map.lookup y env)
      fn _ args = mapM (istriv env x) args >>= bool (return False) (fail "cyclic") . or

-- | Solve to obtain a single instantiation.
solve :: IsTerm term v f => Map v term -> Map v term
solve env =
    if env' == env then env else solve env'
    where env' = Map.map (tsubst env) env

-- | Unification reaching a final solved form (often this isn't needed).
fullunify :: IsTerm term v f => [(term,term)] -> Failing (Map v term)
fullunify eqs = solve <$> unify Map.empty eqs

-- | Examples.
unify_and_apply :: IsTerm term v f => [(term, term)] -> Failing [(term, term)]
unify_and_apply eqs =
    fullunify eqs >>= \i -> return $ List.map (\ (t1, t2) -> (tsubst i t1, tsubst i t2)) eqs

unify_and_apply' :: IsTerm term v f => [(term, term)] -> Failing [(term, term)]
unify_and_apply' eqs =
    mapM app eqs
        where
          app (t1, t2) = fullunify eqs >>= \i -> return $ (tsubst i t1, tsubst i t2)

#ifndef NOTESTS
test01, test02, test03, test04 :: Test
test01 = TestCase (assertEqual "Unify test 1"
                     (Success [(f [f [z],g [y]],
                                f [f [z],g [y]])]) -- expected
                     (unify_and_apply [(f [x, g [y]], f [f [z], w])]))
    where
      [f, g] = [fApp "f", fApp "g"]
      [w, x, y, z] = [vt "w", vt "x", vt "y", vt "z"] :: [MyTerm]
test02 = TestCase (assertEqual "Unify test 2"
                     (Success [(f [y,y],
                                f [y,y])]) -- expected
                     (unify_and_apply [(f [x, y], f [y, x])]))
    where
      [f] = [fApp "f"]
      [x, y] = [vt "x", vt "y"] :: [MyTerm]
test03 = TestCase (assertEqual "Unify test 3"
                     (Failure ["cyclic"]) -- expected
                     (unify_and_apply [(f [x, g [y]], f [y, x])]))
    where
      [f, g] = [fApp "f", fApp "g"]
      [x, y] = [vt "x", vt "y"] :: [MyTerm]
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
      [x_0, x_1, x_2, x_3] = [vt "x0", vt "x1", vt "x2", vt "x3"] :: [MyTerm]
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
#endif
