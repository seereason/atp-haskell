-- | Classes describing constant formulas ('HasBoolean'), formula
-- negation ('IsNegatable') and combination ('IsCombinable'), and the
-- relationship between formulas and the atom type representing the
-- formula's propositional variables ('IsFormula'.)

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Formulas
    ( -- * True and False
      HasBoolean(asBool, fromBool), prettyBool
    , true, false, (⊨), (⊭)
    -- * Negation
    , IsNegatable(naiveNegate, foldNegation, foldNegation'), (.~.), (¬), negate, negated, negative, positive
    -- * IsCombinable
    , IsCombinable((.|.), (.&.), (.<=>.), (.=>.), foldCombination), (.<=.), (.<~>.), (.~|.), (.~&.)
    , (==>), (<=>), (∧), (∨), (⇒), (⇔)
    , BinOp(..), binop
    -- * Formulas
    , IsFormula(atomic, overatoms, onatoms)
    , atom_union
    ) where

import Data.Data (Data)
import Data.Set as Set (Set, empty, union)
import Data.Typeable (Typeable)
import Prelude hiding (negate)
import Pretty (Doc, HasFixity, Pretty, text)

-- |Types that need to have True and False elements.
class HasBoolean p where
    asBool :: p -> Maybe Bool
    fromBool :: Bool -> p
    -- foldBoolean :: (p -> r) -> (Bool -> r) -> p -> r
    -- foldBoolean ho tf fm = maybe (ho fm) tf fm
    -- asBool = foldBoolean Nothing tf

true :: HasBoolean p => p
true = fromBool True

false :: HasBoolean p => p
false = fromBool False

(⊨) :: HasBoolean p => p
(⊨) = true

(⊭) :: HasBoolean p => p
(⊭) = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊨"
prettyBool False = text "⊭"

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'IsLiteral' class.
class IsNegatable formula where
    -- | Negate a formula in a naive fashion, the operators below
    -- prevent double negation.
    naiveNegate :: formula -> formula
    -- | Test whether a formula is negated or normal
    foldNegation :: (formula -> r) -- ^ called for normal formulas
                 -> (formula -> r) -- ^ called for negated formulas
                 -> formula -> r
    foldNegation other ne fm = foldNegation' ne other fm
    foldNegation' :: (formula -> r) -- ^ called for negated formulas
                  -> (formula -> r) -- ^ called for other formulas
                 -> formula -> r

-- | Is this formula negated at the top level?
negated :: IsNegatable formula => formula -> Bool
negated = foldNegation' (not . negated) (const False)

-- | Negate the formula, avoiding double negation
(.~.) :: IsNegatable formula => formula -> formula
(.~.) = foldNegation' id naiveNegate

(¬) :: IsNegatable formula => formula -> formula
(¬) = (.~.)

negate :: IsNegatable formula => formula -> formula
negate = (.~.)

-- | Some operations on IsNegatable formulas
negative :: IsNegatable formula => formula -> Bool
negative = negated

positive :: IsNegatable formula => formula -> Bool
positive = not . negative

infix 5 .~., ¬

-- | A type class for combining logical formulas.  Minimal implementation:
-- @
--  (.|.)
-- @
class IsNegatable formula => IsCombinable formula where
    -- | Disjunction/OR
    (.|.) :: formula -> formula -> formula

    -- | Conjunction/AND.  @x .&. y = (.~.) ((.~.) x .|. (.~.) y)@
    (.&.) :: formula -> formula -> formula
    -- | Equivalence.  @x .<=>. y = (x .=>. y) .&. (y .=>. x)@
    (.<=>.) :: formula -> formula -> formula
    -- | Implication.  @x .=>. y = ((.~.) x .|. y)@
    (.=>.) :: formula -> formula -> formula

    foldCombination :: (formula -> formula -> r) -- disjunction
                    -> (formula -> formula -> r) -- conjunction
                    -> (formula -> formula -> r) -- implication
                    -> (formula -> formula -> r) -- equivalence
                    -> (formula -> r) -- other
                    -> formula -> r

    -- | Reverse implication:
    (.<=.) :: formula -> formula -> formula
    x .<=. y = y .=>. x
    -- | Exclusive or
    (.<~>.) :: formula -> formula -> formula
    x .<~>. y = ((.~.) x .&. y) .|. (x .&. (.~.) y)
    -- | Nor
    (.~|.) :: formula -> formula -> formula
    x .~|. y = (.~.) (x .|. y)
    -- | Nand
    (.~&.) :: formula -> formula -> formula
    x .~&. y = (.~.) (x .&. y)

infixl 1  .<=>. ,  .<~>., ⇔, <=>
infixr 2  .=>., ⇒, ==>
infixl 3  .|., ∨
infixl 4  .&., ∧

(==>) :: IsCombinable formula => formula -> formula -> formula
(==>) = (.=>.)
(<=>) :: IsCombinable formula => formula -> formula -> formula
(<=>) = (.<=>.)

(∧) :: IsCombinable formula => formula -> formula -> formula
(∧) = (.&.)
(∨) :: IsCombinable formula => formula -> formula -> formula
(∨) = (.|.)

-- | ⇒ can't be a function when -XUnicodeSyntax is enabled - it
-- becomes a special character used in type signatures.
(⇒) :: IsCombinable formula => formula -> formula -> formula
(⇒) = (.=>.)
(⇔) :: IsCombinable formula => formula -> formula -> formula
(⇔) = (.<=>.)

data BinOp
    = (:<=>:)
    | (:=>:)
    | (:&:)
    | (:|:)
    deriving (Eq, Ord, Data, Typeable, Show, Enum, Bounded)

-- | Combine formulas with a 'BinOp'.
binop :: IsCombinable formula => formula -> BinOp -> formula -> formula
binop f1 (:<=>:) f2 = f1 .<=>. f2
binop f1 (:=>:) f2 = f1 .=>. f2
binop f1 (:&:) f2 = f1 .&. f2
binop f1 (:|:) f2 = f1 .|. f2

-- | Class associating a formula type with its atom (atomic formula) type.
class (Pretty formula, HasFixity formula, Eq atom, Ord atom, Pretty atom, HasFixity atom)
    => IsFormula formula atom | formula -> atom where
    atomic :: atom -> formula
    -- ^ Build a formula from an atom.
    overatoms :: (atom -> r -> r) -> formula -> r -> r
    -- ^ Formula analog of iterator 'foldr'.
    onatoms :: (atom -> formula) -> formula -> formula
    -- ^ Apply a function to the atoms, otherwise keeping structure.

-- | Special case of a union of the results of a function over the atoms.
atom_union :: (IsFormula formula atom, Ord r) => (atom -> Set r) -> formula -> Set r
atom_union f fm = overatoms (\h t -> Set.union (f h) t) fm Set.empty
