{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

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
    ) where

import Data.Monoid ((<>))
import Language.Haskell.TH.Syntax (maxPrecedence)
import Language.Haskell.TH.Ppr (noPrec, Precedence)
import Text.PrettyPrint.HughesPJClass (braces, brackets, Doc, Pretty(pPrint), nest, parens, prettyShow, text)
import Data.List as List (intercalate, map, sort)
import Data.Map as Map (Map, toList)
import Data.Set as Set (Set, toAscList)

data Associativity
    = InfixL  -- Left-associative - a-b-c == (a-b)-c
    | InfixR  -- Right-associative - a=>b=>c == a=>(b=>c)
    | InfixN  -- Non-associative - a>b>c is an error
    | InfixA  -- Associative - a+b+c == (a+b)+c == a+(b+c)

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
parenthesize :: Fixity -> Fixity -> Side -> Doc -> Doc
parenthesize (Fixity pprec pdir) (Fixity prec _dir) side pp =
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
            (_, InfixN) -> error "Nested non-associative operators"

instance Pretty a => Pretty (Set a) where
    -- pPrint s = text "{" <> mconcat (intersperse (text ", ") (List.map pPrint (Set.toAscList s))) <> text "}"
    pPrint s = text "{" <> text (intercalate ", " (List.sort (List.map prettyShow (Set.toAscList s)))) <> text "}"

instance (Pretty v, Pretty term) => Pretty (Map v term) where
    pPrint = pPrint . Map.toList
