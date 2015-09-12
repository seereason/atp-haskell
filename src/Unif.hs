-- | Unification for first order terms.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
module Unif
    ( unify
    , solve
    , fullunify
    , unify_and_apply
    , tests
    ) where

import Lib (Failing(Success, Failure), failing)
import FOL (IsTerm(..), tsubst)
import Skolem (MyTerm)
import Data.List as List (map)
import Data.Map as Map
import Test.HUnit

-- | Main unification procedure
unify :: IsTerm term v f => Map v term -> [(term,term)] -> Failing (Map v term)
unify env [] = Success env
unify env ((a,b):oth) =
    foldTerm (vr b) (\ f fargs -> foldTerm (vr a) (fn f fargs) b) a
    where
      vr t x =
          maybe (istriv env x t >>= \ trivial -> unify (if trivial then env else Map.insert x t env) oth)
                (\ y -> unify env ((y, t) : oth))
                (Map.lookup x env)
      fn f fargs g gargs =
          if f == g && length fargs == length gargs
          then unify env (zip fargs gargs ++ oth)
          else Failure ["impossible unification"]

istriv :: IsTerm term v f => Map.Map v term -> v -> term -> Failing Bool
istriv env x t =
    foldTerm v f t
    where
      v y =
          if x == y
          then Success True
          else maybe (Success False) (istriv env x) (Map.lookup y env)
      f _ args =
          if any (failing (const False) id . istriv env x) args
          then Failure ["cyclic"]
          else Success False

-- | Solve to obtain a single instantiation.
solve :: (IsTerm term v f, Eq term) => Map v term -> Map v term
solve env =
    if env' == env then env else solve env'
    where env' = Map.map (tsubst env) env

-- | Unification reaching a final solved form (often this isn't needed).
fullunify :: (IsTerm term v f, Eq term) => [(term,term)] -> Failing (Map v term)
fullunify eqs = failing Failure (Success . solve) (unify Map.empty eqs)

-- | Examples.
unify_and_apply :: (IsTerm term v f, Eq term) => [(term, term)] -> Failing [(term, term)]
unify_and_apply eqs =
    case fullunify eqs of
      Failure x -> Failure x
      Success i -> Success (List.map (\ (t1, t2) -> (tsubst i t1, tsubst i t2)) eqs)

unify_and_apply' :: (Eq term, IsTerm term v function) => [(term, term)] -> Failing [(term, term)]
unify_and_apply' eqs =
    mapM app eqs
        where
          app (t1, t2) = failing Failure (\ i -> Success (tsubst i t1, tsubst i t2)) (fullunify eqs)

test01 :: Test
test01 = TestCase $ assertEqual "Unify tests" expected input
    where input = List.map unify_and_apply eqss
          f = fApp "f"
          g = fApp "g"
          w = vt "w" :: MyTerm
          x = vt "x" :: MyTerm
          x_0 = vt "x0" :: MyTerm
          x_1 = vt "x1" :: MyTerm
          x_2 = vt "x2" :: MyTerm
          x_3 = vt "x3" :: MyTerm
          y = vt "y" :: MyTerm
          z = vt "z" :: MyTerm
          expected = List.map Success $
                      [[(f [f [z],g [y]],
                         f [f [z],g [y]])],
                       [(f [y,y],
                         f [y,y])],
                       [(f [f [f [x_3,x_3],f [x_3,x_3]], f [f [x_3,x_3],f [x_3,x_3]]],
                         f [f [f [x_3,x_3],f [x_3,x_3]], f [f [x_3,x_3],f [x_3,x_3]]]),
                        (f [f [x_3,x_3],f [x_3,x_3]],
                         f [f [x_3,x_3],f [x_3,x_3]]),
                        (f [x_3,x_3],
                         f [x_3,x_3])]]
          eqss :: [[(MyTerm, MyTerm)]]
          eqss =  [ [(f [x, g [y]], f [f [z], w])]
                  , [(f [x, y], f [y, x])]
                  -- , [(f [x, g [y]], f [y, x])] -- cyclic
                  , [(x_0, f [x_1, x_1]),
                     (x_1, f [x_2, x_2]),
                     (x_2, f [x_3, x_3])] ]
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

tests = TestList [test01]
