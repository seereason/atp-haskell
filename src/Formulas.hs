-- | Classes describing constant formulas ('HasBoolean'), formula
-- negation ('IsNegatable') and combination ('IsCombinable'), and the
-- relationship between formulas and the atom type representing the
-- formula's propositional variables ('IsFormula'.)

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Formulas
    ( -- * True and False
      HasBoolean(asBool, fromBool), prettyBool
    , true, false, (⊥), (⊤)
    -- * Negation
    , IsNegatable(naiveNegate, foldNegation), (.~.), (¬), negate, negated, negative, positive
    -- * Formulas
    , IsAtom
    , IsFormula(AtomOf, atomic, overatoms, onatoms)
    , atom_union
    ) where

import Data.Data (Data)
import Data.Set as Set (Set, empty, union)
import Data.Typeable (Typeable)
import Language.Haskell.TH (Dec(InfixD), Fixity(Fixity), FixityDirection(InfixN, InfixL, InfixR))
import Prelude hiding (negate)
import Pretty (Doc, HasFixity, notPrec, Pretty,
               text, iffPrec, impPrec, andPrec, orPrec)

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

(⊤) :: HasBoolean p => p
(⊤) = true

(⊥) :: HasBoolean p => p
(⊥) = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊤"
prettyBool False = text "⊥"

-- | The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean logic
-- operators, such as the 'IsLiteral' class.
class IsNegatable formula where
    -- | Negate a formula in a naive fashion, the operators below
    -- prevent double negation.
    naiveNegate :: formula -> formula
    -- | Test whether a formula is negated or normal
    foldNegation :: (formula -> r) -- ^ called for normal formulas
                 -> (formula -> r) -- ^ called for negated formulas
                 -> formula -> r

-- | Is this formula negated at the top level?
negated :: IsNegatable formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

-- | Negate the formula, avoiding double negation
(.~.), (¬), negate :: IsNegatable formula => formula -> formula
(.~.) = foldNegation naiveNegate id
(¬) = (.~.)
negate = (.~.)
infix 6 .~., ¬

-- | Some operations on IsNegatable formulas
negative :: IsNegatable formula => formula -> Bool
negative = negated

positive :: IsNegatable formula => formula -> Bool
positive = not . negative

-- | Basic properties of an atomic formula
class (Ord atom, Show atom, HasFixity atom, Pretty atom) => IsAtom atom

-- | Class associating a formula type with its atom (atomic formula) type.
class (Pretty formula, HasFixity formula, IsAtom (AtomOf formula)) => IsFormula formula where
    type AtomOf formula
    -- ^ AtomOf is a function that maps the formula type to the associated atom type
    atomic :: AtomOf formula -> formula
    -- ^ Build a formula from an atom.
    overatoms :: (AtomOf formula -> r -> r) -> formula -> r -> r
    -- ^ Formula analog of iterator 'foldr'.
    onatoms :: (AtomOf formula -> formula) -> formula -> formula
    -- ^ Apply a function to the atoms, otherwise keeping structure.

-- | Special case of a union of the results of a function over the atoms.
atom_union :: (IsFormula formula, Ord r) => (AtomOf formula -> Set r) -> formula -> Set r
atom_union f fm = overatoms (\h t -> Set.union (f h) t) fm Set.empty
