{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
module Pretty
    ( Pretty(pPrint)
    , module Text.PrettyPrint.HughesPJClass
    , HasFixity(fixity)
    , TH.Fixity(..)
    , TH.FixityDirection(..)
    , topFixity
    , botFixity
    ) where

import qualified Language.Haskell.TH.Syntax as TH
import Text.PrettyPrint.HughesPJClass (Doc, Pretty(pPrint), nest, parens, prettyShow, text, (<>))
import Data.List as List (intercalate, map, sort)
import Data.Map as Map (Map, map, mapKeys)
import Data.Set as Set (Set, map, toAscList)

-- | A class used to do proper parenthesization of formulas.  If we
-- nest a higher precedence formula inside a lower one parentheses can
-- be omitted.  Because @|@ has lower precedence than @&@, the formula
-- @a | (b & c)@ appears as @a | b & c@, while @(a | b) & c@ appears
-- unchanged.  (Name Precedence chosen because Fixity was taken.)
-- 
-- The second field of Fixity is the FixityDirection, which can be
-- left, right, or non.  A left associative operator like @/@ is
-- grouped left to right, so parenthese can be omitted from @(a / b) /
-- c@ but not from @a / (b / c)@.  It is a syntax error to omit
-- parentheses when formatting a non-associative operator.
-- 
-- The Haskell FixityDirection type is concerned with how to interpret
-- a formula formatted in a certain way, but here we are concerned
-- with how to format a formula given its interpretation.  As such,
-- one case the Haskell type does not capture is whether the operator
-- follows the associative law, so we can omit parentheses in an
-- expression such as @a & b & c@.
class HasFixity x where
    fixity :: x -> TH.Fixity

-- Definitions from template-haskell:
-- data Fixity = Fixity Int FixityDirection
-- data FixityDirection = InfixL | InfixR | InfixN

-- | This is used as the initial value for the parent fixity.
topFixity :: TH.Fixity
topFixity = TH.Fixity 0 TH.InfixN

-- | This is used as the fixity for things that never need
-- parenthesization, such as function application or a variable name.
botFixity :: TH.Fixity
botFixity = TH.Fixity 10 TH.InfixN

instance HasFixity String where
    fixity _ = botFixity

-- | Wrapper to indicate we want show to render the expression using
-- class methods to build a value, not the show derived for the
-- specific instance.
newtype Classy a = Classy {deClassy :: a} deriving (Eq, Ord)

instance Show (Classy a) => Show (Classy [a]) where
    show = show . List.map Classy . deClassy

instance (Show (Classy a), Show (Classy b)) => Show (Classy (a, b)) where
    show (Classy (a, b)) = show (Classy a, Classy b)

instance (Show (Classy a), Show (Classy b), Show (Classy c)) => Show (Classy (a, b, c)) where
    show (Classy (a, b, c)) = show (Classy a, Classy b, Classy c)

instance (Show (Classy a), Show (Classy b), Show (Classy c), Show (Classy d)) => Show (Classy (a, b, c, d)) where
    show (Classy (a, b, c, d)) = show (Classy a, Classy b, Classy c, Classy d)

instance (Ord a, Show (Classy a)) => Show (Classy (Set a)) where
    show (Classy s) = show (Set.map Classy s)

instance (Ord k, Show (Classy k), Show (Classy v)) => Show (Classy (Map k v)) where
    show (Classy mp) = show . Map.mapKeys Classy . Map.map Classy $ mp

instance Show (Classy Bool) where
    show = show . deClassy

instance Show (Classy Int) where
    show = show . deClassy

instance Pretty a => Pretty (Set a) where
    -- pPrint s = text "{" <> mconcat (intersperse (text ", ") (List.map pPrint (Set.toAscList s))) <> text "}"
    pPrint s = text "{" <> text (intercalate ", " (List.sort (List.map prettyShow (Set.toAscList s)))) <> text "}"