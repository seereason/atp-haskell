-- | The 'IsFormula' class contains definitions for the boolean true
-- and false values, and methods for traversing the atoms of a formula.

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Logic.ATP.Formulas
    ( IsAtom
    , IsFormula(AtomOf, true, false, asBool, atomic, overatoms, onatoms)
    , (⊥), (⊤)
    , fromBool
    , prettyBool
    , atom_union
    ) where

import Data.Logic.ATP.Pretty (Doc, HasFixity, Pretty, text)
import Data.Set as Set (Set, empty, union)
import Prelude hiding (negate)

-- | Basic properties of an atomic formula
class (Ord atom, Show atom, HasFixity atom, Pretty atom) => IsAtom atom

-- | Class associating a formula type with its atom (atomic formula) type.
class (Pretty formula, HasFixity formula, IsAtom (AtomOf formula)) => IsFormula formula where
    type AtomOf formula
    -- ^ AtomOf is a function that maps the formula type to the
    -- associated atomic formula type
    true :: formula
    -- ^ The true element
    false :: formula
    -- ^ The false element
    asBool :: formula -> Maybe Bool
    -- ^ If the arugment is true or false return the corresponding
    -- 'Bool', otherwise return 'Nothing'.
    atomic :: AtomOf formula -> formula
    -- ^ Build a formula from an atom.
    overatoms :: (AtomOf formula -> r -> r) -> formula -> r -> r
    -- ^ Formula analog of iterator 'foldr'.
    onatoms :: (AtomOf formula -> AtomOf formula) -> formula -> formula
    -- ^ Apply a function to the atoms, otherwise keeping structure (new sig)

(⊤) :: IsFormula p => p
(⊤) = true

(⊥) :: IsFormula p => p
(⊥) = false

fromBool :: IsFormula formula => Bool -> formula
fromBool True = true
fromBool False = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊤"
prettyBool False = text "⊥"

-- | Special case of a union of the results of a function over the atoms.
atom_union :: (IsFormula formula, Ord r) => (AtomOf formula -> Set r) -> formula -> Set r
atom_union f fm = overatoms (\h t -> Set.union (f h) t) fm Set.empty
