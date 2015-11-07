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
    -- * Formulas
    , IsAtom
    , IsFormula(AtomOf, atomic, overatoms, onatoms)
    , atom_union
    ) where

import Data.Set as Set (Set, empty, union)
import Prelude hiding (negate)
import Pretty (Doc, HasFixity, Pretty, text)

-- |Types that need to have True and False elements.  This is the most
-- basic feature of a formula.
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

-- | Basic properties of an atomic formula
class (Ord atom, Show atom, HasFixity atom, Pretty atom) => IsAtom atom

-- | Class associating a formula type with its atom (atomic formula) type.
class (HasBoolean formula, Pretty formula, HasFixity formula, IsAtom (AtomOf formula)) => IsFormula formula where
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
