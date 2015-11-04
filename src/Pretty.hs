{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pretty
    ( (<>)
    , Pretty(pPrint)
    , module Text.PrettyPrint.HughesPJClass
    , HasFixity(fixity)
    , Side(LHS, RHS, Unary)
    , Fixity(Fixity)
    , Associativity(InfixL, InfixR, InfixN, InfixA)
    , rootFixity
    , leafFixity
    , parenthesize
    , assertEqual'
    ) where

import Control.Monad (unless)
import Data.Map as Map (Map, toList)
import Data.Monoid ((<>))
import Data.Set as Set (Set, toAscList)
import GHC.Stack
import Language.Haskell.TH.Syntax (maxPrecedence)
import Language.Haskell.TH.Ppr (noPrec, Precedence)
import Test.HUnit (Assertion, assertFailure)
import Text.PrettyPrint.HughesPJClass (brackets, comma, Doc, fsep, hcat, nest, Pretty(pPrint), prettyShow, punctuate, text)

data Associativity
    = InfixL  -- Left-associative - a-b-c == (a-b)-c
    | InfixR  -- Right-associative - a=>b=>c == a=>(b=>c)
    | InfixN  -- Non-associative - a>b>c is an error
    | InfixA  -- Associative - a+b+c == (a+b)+c == a+(b+c), ~~a == ~(~a)

data Fixity = Fixity Precedence Associativity

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
    fixity :: x -> Fixity

defaultFixity :: Fixity
defaultFixity = Fixity maxPrecedence InfixL

-- Definitions from template-haskell:
-- data Fixity = Fixity Int FixityDirection
-- data FixityDirection = InfixL | InfixR | InfixN

-- | This is used as the initial value for the parent fixity.
leafFixity :: Fixity
leafFixity = defaultFixity

-- | This is used as the fixity for things that never need
-- parenthesization, such as function application or a variable name.
rootFixity :: Fixity
rootFixity = Fixity noPrec InfixN

instance HasFixity String where
    fixity _ = leafFixity

data Side = LHS | RHS | Unary

-- | Combine the parent and child fixities to determine whether the
-- child formula should be parenthesized.
parenthesize :: (Monoid r, Show r) => (r -> r) -> (r -> r) -> Fixity -> Fixity -> Side -> r -> r
parenthesize parens braces (Fixity pprec pdir) (Fixity prec _dir) side pp =
    -- If fixity goes in the "wrong direction" we need to add parens.
    -- leafFixity is the highest, so if the parent fixity is greater
    -- we need parens: fixity(~)=5, fixity(|)=3, so ~(a|b) needs
    -- parens, (~a)|b does not.
    case compare pprec prec of
      GT -> parens pp
      LT | pprec == 3 && prec == 4 -> parens pp -- always parenthesize ands of ors and ors of ands - too confusing
      LT -> pp
      EQ ->
          -- Similarly for fixity direction, if parent and child have
          -- the same precedence and the parent operator has left
          -- fixity, we need parens if we are rendering the right
          -- child.  So a-(b-c) needs parens, but (a-b)-c does not.
          -- For InfixR, (a=>b)=>c needs parens, while a=>(b=>c) does
          -- not.
          case (side, pdir) of
            (LHS, InfixL) -> pp
            (RHS, InfixL) -> parens pp
            (LHS, InfixR) -> parens pp
            (RHS, InfixR) -> pp
            (_, InfixA) -> pp
            (Unary, _) -> braces pp -- not sure
            (_, InfixN) -> error ("Nested non-associative operators: " ++ show pp)

instance Pretty a => Pretty (Set a) where
    pPrint = brackets . fsep . punctuate comma . map pPrint . Set.toAscList

instance (Pretty v, Pretty term) => Pretty (Map v term) where
    pPrint = pPrint . Map.toList

-- | Version of assertEqual that uses the pretty printer instead of show.
assertEqual' :: (?loc :: CallStack, Eq a, Pretty a) =>
                String -- ^ The message prefix
             -> a      -- ^ The expected value
             -> a      -- ^ The actual value
             -> Assertion
assertEqual' preface expected actual =
  unless (actual == expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ prettyShow expected ++ "\n but got: " ++ prettyShow actual
