{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Logic.ATP.Pretty
    ( (<>)
    , Pretty(pPrint, pPrintPrec)
    , module Text.PrettyPrint.HughesPJClass
    , Associativity(InfixL, InfixR, InfixN, InfixA)
    , Precedence
    , HasFixity(precedence, associativity)
    , Side(Top, LHS, RHS, Unary)
    , testParen
    -- , parenthesize
    , assertEqual'
    , testEquals
    , leafPrec
    , boolPrec
    , notPrec
    , atomPrec
    , andPrec
    , orPrec
    , impPrec
    , iffPrec
    , quantPrec
    , eqPrec
    , pAppPrec
    ) where

import Control.Monad (unless)
import Data.Map.Strict as Map (Map, toList)
import Data.Monoid ((<>))
import Data.Set as Set (Set, toAscList)
import GHC.Stack
import Language.Haskell.TH (ExpQ, litE, stringL)
import Test.HUnit (Assertion, assertFailure, Test(TestLabel, TestCase))
import Text.PrettyPrint.HughesPJClass (brackets, comma, Doc, fsep, hcat, nest, Pretty(pPrint, pPrintPrec), prettyShow, punctuate, text)

-- | A class to extract the fixity of a formula so they can be
-- properly parenthesized.
--
-- The Haskell FixityDirection type is concerned with how to interpret
-- a formula formatted in a certain way, but here we are concerned
-- with how to format a formula given its interpretation.  As such,
-- one case the Haskell type does not capture is whether the operator
-- follows the associative law, so we can omit parentheses in an
-- expression such as @a & b & c@.  Hopefully, we can generate
-- formulas so that an associative operator with left associative
-- fixity direction appears as (a+b)+c rather than a+(b+c).
class HasFixity x where
    precedence :: x -> Precedence
    precedence _ = leafPrec
    associativity :: x -> Associativity
    associativity _ = InfixL

-- | Use the same precedence type as the pretty package
type Precedence = forall a. Num a => a

data Associativity
    = InfixL  -- Left-associative - a-b-c == (a-b)-c
    | InfixR  -- Right-associative - a=>b=>c == a=>(b=>c)
    | InfixN  -- Non-associative - a>b>c is an error
    | InfixA  -- Associative - a+b+c == (a+b)+c == a+(b+c), ~~a == ~(~a)
    deriving Show

-- | What side of the parent formula are we rendering?
data Side = Top | LHS | RHS | Unary deriving Show

-- | Decide whether to parenthesize based on which side of the parent binary
-- operator we are rendering, the parent operator's precedence, and the precedence
-- and associativity of the operator we are rendering.
-- testParen :: Side -> Precedence -> Precedence -> Associativity -> Bool
testParen :: (Eq a, Ord a, Num a) => Side -> a -> a -> Associativity -> Bool
testParen side parentPrec childPrec childAssoc =
    testPrecedence || (parentPrec == childPrec && testAssoc)
    -- parentPrec > childPrec || (parentPrec == childPrec && testAssoc)
    where
      testPrecedence =
          parentPrec > childPrec ||
          (parentPrec == orPrec && childPrec == andPrec) -- Special case - I can't keep these straight
      testAssoc = case (side, childAssoc) of
                    (LHS, InfixL) -> False
                    (RHS, InfixR) -> False
                    (_, InfixA) -> False
                    -- Tests from the previous version.
                    -- (RHS, InfixL) -> True
                    -- (LHS, InfixR) -> True
                    -- (Unary, _) -> braces pp -- not sure
                    -- (_, InfixN) -> error ("Nested non-associative operators: " ++ show pp)
                    _ -> True

instance Pretty a => Pretty (Set a) where
    pPrint = brackets . fsep . punctuate comma . map pPrint . Set.toAscList

instance (Pretty v, Pretty term) => Pretty (Map v term) where
    pPrint = pPrint . Map.toList

-- | Version of assertEqual that uses the pretty printer instead of show.
assertEqual' :: (
#ifndef ghcjs_HOST_OS
                 ?loc :: CallStack,
#endif
                 Eq a, Pretty a) =>
                String -- ^ The message prefix
             -> a      -- ^ The expected value
             -> a      -- ^ The actual value
             -> Assertion
assertEqual' preface expected actual =
  unless (actual == expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ prettyShow expected ++ "\n but got: " ++ prettyShow actual

testEquals :: String -> ExpQ
testEquals label = [| \expected actual -> TestLabel $(litE (stringL label)) $ TestCase $ assertEqual' $(litE (stringL label)) expected actual|]

leafPrec :: Num a => a
leafPrec = 9

atomPrec :: Num a => a
atomPrec = 7
notPrec :: Num a => a
notPrec = 6
andPrec :: Num a => a
andPrec = 5
orPrec :: Num a => a
orPrec = 4
impPrec :: Num a => a
impPrec = 3
iffPrec :: Num a => a
iffPrec = 2
boolPrec :: Num a => a
boolPrec = leafPrec
quantPrec :: Num a => a
quantPrec = 1
eqPrec :: Num a => a
eqPrec = 6
pAppPrec :: Num a => a
pAppPrec = 9
