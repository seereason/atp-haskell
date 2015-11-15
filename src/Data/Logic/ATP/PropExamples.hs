-- | Some propositional formulas to test, and functions to generate classes.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.Logic.ATP.PropExamples
    ( Knows(K)
    , mk_knows, mk_knows2
    , prime
    , ramsey
    , testPropExamples
    ) where

import Data.Bits (Bits, shiftR)
import Data.List as List (map)
import Data.Logic.ATP.Formulas
import Data.Logic.ATP.Lib (allsets, timeMessage)
import Data.Logic.ATP.Lit ((.~.))
import Data.Logic.ATP.Pretty (HasFixity(precedence), Pretty(pPrint), prettyShow, text)
import Data.Logic.ATP.Prop
import Data.Set as Set
import Prelude hiding (sum)
import Test.HUnit

-- | Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t)
ramsey :: (IsPropositional pf, AtomOf pf ~ Knows Integer, Ord pf) =>
          Integer -> Integer -> Integer -> pf
ramsey s t n =
  let vertices = Set.fromList [1 .. n] in
  let yesgrps = Set.map (allsets (2 :: Integer)) (allsets s vertices)
      nogrps = Set.map (allsets (2 :: Integer)) (allsets t vertices) in
  let e xs = let [a, b] = Set.toAscList xs in atomic (K "p" a (Just b)) in
  list_disj (Set.map (list_conj . Set.map e) yesgrps) .|. list_disj (Set.map (list_conj . Set.map (\ p -> (.~.)(e p))) nogrps)

data Knows a = K String a (Maybe a) deriving (Eq, Ord, Show)

instance (Num a, Show a) => Pretty (Knows a) where
    pPrint (K s n mm) = text (s ++ show n ++ maybe "" (\ m -> "." ++ show m) mm)

instance Num a => HasFixity (Knows a) where
    precedence _ = 9

instance IsAtom (Knows Integer)

-- Some currently tractable examples. (p. 36)
test01 :: Test
test01 = TestList [TestCase (assertEqual "ramsey 3 3 4"
                                         "(p1.2∧p1.3∧p2.3)∨(p1.2∧p1.4∧p2.4)∨(p1.3∧p1.4∧p3.4)∨(p2.3∧p2.4∧p3.4)∨(¬p1.2∧¬p1.3∧¬p2.3)∨(¬p1.2∧¬p1.4∧¬p2.4)∨(¬p1.3∧¬p1.4∧¬p3.4)∨(¬p2.3∧¬p2.4∧¬p3.4)"
                                         -- "p1.2∧p1.3∧p2.3∨p1.2∧p1.4∧p2.4∨p1.3∧p1.4∧p3.4∨p2.3∧p2.4∧p3.4∨¬p1.2∧¬p1.3∧¬p2.3∨¬p1.2∧¬p1.4∧¬p2.4∨¬p1.3∧¬p1.4∧¬p3.4∨¬p2.3∧¬p2.4∧¬p3.4"
                                         (prettyShow (ramsey 3 3 4 :: PFormula (Knows Integer)))),
                   TestCase (timeMessage (\_ t -> "\nTime to compute (ramsey 3 3 5): " ++ show t) $ assertEqual "tautology (ramsey 3 3 5)" False (tautology (ramsey 3 3 5 :: PFormula (Knows Integer)))),
                   TestCase (timeMessage (\_ t -> "\nTime to compute (ramsey 3 3 6): " ++ show t) $ assertEqual "tautology (ramsey 3 3 6)" True (tautology (ramsey 3 3 6 :: PFormula (Knows Integer))))]

-- | Half adder.  (p. 66)
halfsum :: forall formula. IsPropositional formula => formula -> formula -> formula
halfsum x y = x .<=>. ((.~.) y)

halfcarry :: forall formula. IsPropositional formula => formula -> formula -> formula
halfcarry x y = x .&. y

ha :: forall formula. IsPropositional formula => formula -> formula -> formula -> formula -> formula
ha x y s c = (s .<=>. halfsum x y) .&. (c .<=>. halfcarry x y)

-- | Full adder.
carry :: forall formula. IsPropositional formula => formula -> formula -> formula -> formula
carry x y z = (x .&. y) .|. ((x .|. y) .&. z)

sum :: forall formula. IsPropositional formula => formula -> formula -> formula -> formula
sum x y z = halfsum (halfsum x y) z

fa :: forall formula. IsPropositional formula => formula -> formula -> formula -> formula -> formula -> formula
fa x y z s c = (s .<=>. sum x y z) .&. (c .<=>. carry x y z)

-- | Useful idiom.
conjoin :: (IsPropositional formula, Ord formula, Ord a) => (a -> formula) -> Set a -> formula
conjoin f l = list_conj (Set.map f l)

-- | n-bit ripple carry adder with carry c(0) propagated in and c(n) out.  (p. 67)
ripplecarry :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> a -> formula
ripplecarry x y c out n =
    conjoin (\ i -> fa (x i) (y i) (c i) (out i) (c(i + 1))) (Set.fromList [0 .. (n - 1)])

-- Example.
mk_knows :: (IsPropositional formula, AtomOf formula ~ Knows a) => String -> a -> formula
mk_knows x i = atomic (K x i Nothing)
mk_knows2 :: (IsPropositional formula, AtomOf formula ~ Knows a) => String -> a -> a -> formula
mk_knows2 x i j = atomic (K x i (Just j))

test02 :: Test
test02 =
    let [x, y, out, c] = List.map mk_knows ["X", "Y", "OUT", "C"] :: [Integer -> PFormula (Knows Integer)] in
    TestCase (assertEqual "ripplecarry x y c out 2"
                          (((out 0 .<=>. ((x 0 .<=>. ((.~.) (y 0))) .<=>. ((.~.) (c 0)))) .&.
                            (c 1 .<=>. ((x 0 .&. y 0) .|. ((x 0 .|. y 0) .&. c 0)))) .&.
                           ((out 1 .<=>. ((x 1 .<=>. ((.~.) (y 1))) .<=>. ((.~.) (c 1)))) .&.
                            (c 2 .<=>. ((x 1 .&. y 1) .|. ((x 1 .|. y 1) .&. c 1)))))
                          (ripplecarry x y c out 2 :: PFormula (Knows Integer)))

-- | Special case with 0 instead of c(0).
ripplecarry0 :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
                (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> a -> formula
ripplecarry0 x y c out n =
  psimplify
   (ripplecarry x y (\ i -> if i == 0 then false else c i) out n)

-- | Carry-select adder
ripplecarry1 :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
                (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> a -> formula
ripplecarry1 x y c out n =
  psimplify
   (ripplecarry x y (\ i -> if i == 0 then true else c i) out n)

mux :: forall formula. IsPropositional formula => formula -> formula -> formula -> formula
mux sel in0 in1 = (((.~.) sel) .&. in0) .|. (sel .&. in1)

offset :: forall t a. Num a => a -> (a -> t) -> a -> t
offset n x i = x (n + i)

carryselect :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> a -> a -> formula
carryselect x y c0 c1 s0 s1 c s n k =
  let k' = min n k in
  let fm = ((ripplecarry0 x y c0 s0 k') .&. (ripplecarry1 x y c1 s1 k')) .&.
           (((c k') .<=>. (mux (c 0) (c0 k') (c1 k'))) .&.
            (conjoin (\ i -> (s i) .<=>. (mux (c 0) (s0 i) (s1 i)))
                             (Set.fromList [0 .. (k' - 1)]))) in
  if k' < k then fm else
  fm .&. (carryselect
          (offset k x) (offset k y) (offset k c0) (offset k c1)
          (offset k s0) (offset k s1) (offset k c) (offset k s)
          (n - k) k)

-- | Equivalence problems for carry-select vs ripple carry adders. (p. 69)
mk_adder_test :: (IsPropositional formula, Ord formula, AtomOf formula ~ Knows a, Ord a, Num a, Enum a) =>
                 a -> a -> formula
mk_adder_test n k =
  let [x, y, c, s, c0, s0, c1, s1, c2, s2] =
          List.map mk_knows ["x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2"] in
  (((carryselect x y c0 c1 s0 s1 c s n k) .&.
    ((.~.) (c 0))) .&.
   (ripplecarry0 x y c2 s2 n)) .=>.
  (((c n) .<=>. (c2 n)) .&.
   (conjoin (\ i -> (s i) .<=>. (s2 i)) (Set.fromList [0 .. (n - 1)])))

-- | Ripple carry stage that separates off the final result.  (p. 70)
--
--       UUUUUUUUUUUUUUUUUUUU  (u)
--    +  VVVVVVVVVVVVVVVVVVVV  (v)
--
--    = WWWWWWWWWWWWWWWWWWWW   (w)
--    +                     Z  (z)

rippleshift :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> formula
            -> (a -> formula)
            -> a -> formula
rippleshift u v c z w n =
  ripplecarry0 u v (\ i -> if i == n then w(n - 1) else c(i + 1))
                   (\ i -> if i == 0 then z else w(i - 1)) n

-- | Naive multiplier based on repeated ripple carry.
multiplier :: (IsPropositional formula, Ord formula, Ord a, Num a, Enum a) =>
              (a -> a -> formula)
           -> (a -> a -> formula)
           -> (a -> a -> formula)
           -> (a -> formula)
           -> a
           -> formula
multiplier x u v out n =
  if n == 1 then ((out 0) .<=>. (x 0 0)) .&. ((.~.)(out 1)) else
  psimplify (((out 0) .<=>. (x 0 0)) .&.
             ((rippleshift
               (\ i -> if i == n - 1 then false else x 0 (i + 1))
               (x 1) (v 2) (out 1) (u 2) n) .&.
              (if n == 2 then ((out 2) .<=>. (u 2 0)) .&. ((out 3) .<=>. (u 2 1)) else
                   conjoin (\ k -> rippleshift (u k) (x k) (v(k + 1)) (out k)
                                   (if k == n - 1 then \ i -> out(n + i)
                                    else u(k + 1)) n) (Set.fromList [2 .. (n - 1)]))))

-- | Primality examples. (p. 71)
--
-- For large examples, should use 'Integer' instead of 'Int' in these functions.
bitlength :: forall b a. (Num a, Num b, Bits b) => b -> a
bitlength x = if x == 0 then 0 else 1 + bitlength (shiftR x 1);;

bit :: forall a b. (Num a, Eq a, Bits b, Integral b) => a -> b -> Bool
bit n x = if n == 0 then x `mod` 2 == 1 else bit (n - 1) (shiftR x 1)

congruent_to :: (IsPropositional formula, Ord formula, Bits b, Ord a, Num a, Integral b, Enum a) =>
                (a -> formula) -> b -> a -> formula
congruent_to x m n =
  conjoin (\ i -> if bit i m then x i else (.~.)(x i))
          (Set.fromList [0 .. (n - 1)])

prime :: (IsPropositional formula, Ord formula, AtomOf formula ~ Knows Integer) => Integer -> formula
prime p =
  let [x, y, out] = List.map mk_knows ["x", "y", "out"] in
  let m i j = (x i) .&. (y j)
      [u, v] = List.map mk_knows2 ["u", "v"] in
  let (n :: Integer) = bitlength p in
  (.~.) (multiplier m u v out (n - 1) .&. congruent_to out p (max n (2 * n - 2)))

-- Examples. (p. 72)

type F = PFormula (Knows Integer)

test03 :: Test
test03 =
    TestList [TestCase (timeMessage (\_ t -> "\nTime to prove (prime 7): " ++ show t)  (assertEqual "tautology(prime 7)" True (tautology (prime 7 :: F)))),
              TestCase (timeMessage (\_ t -> "\nTime to prove (prime 9): " ++ show t)  (assertEqual "tautology(prime 9)" False (tautology (prime 9 :: F)))),
              TestCase (timeMessage (\_ t -> "\nTime to prove (prime 11): " ++ show t) (assertEqual "tautology(prime 11)" True (tautology (prime 11 :: F))))]

testPropExamples :: Test
testPropExamples = TestLabel "PropExamples" (TestList [test01, test02, test03])
