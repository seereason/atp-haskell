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
    -- * IsCombinable
    , IsCombinable((.|.), (.&.), (.<=>.), (.=>.), foldCombination),
      (.<=.), (.<~>.), (.~|.), (.~&.)
    , (⇒), (==>), (⊃), (→)
    , (⇔), (<=>), (↔)
    , (∧), (·)
    , (∨)
    , BinOp(..), binop
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

-- | A type class for combining logical formulas.  Minimal implementation:
-- @
--  (.|.), (.&.), (.=>.), (.<=>.)
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

    foldCombination :: (formula -> r) -- other
                    -> (formula -> formula -> r) -- disjunction
                    -> (formula -> formula -> r) -- conjunction
                    -> (formula -> formula -> r) -- implication
                    -> (formula -> formula -> r) -- equivalence
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

infixl 3 .<=.
infixl 2 .<~>.

-- | Implication synonyms.  Note that if the -XUnicodeSyntax option is
-- turned on the operator ⇒ can not be declared/used as a function -
-- it becomes a reserved special character used in type signatures.
(⇒), (⊃), (==>), (→) :: IsCombinable formula => formula -> formula -> formula
(⇒) = (.=>.)
(⊃) = (.=>.)
(==>) = (.=>.)
(→) = (.=>.)
infixr 3 .=>., ⇒, ⊃, ==>, →

-- | If-and-only-if synonyms
(<=>), (<==>), (⇔), (↔) :: IsCombinable formula => formula -> formula -> formula
(<=>) = (.<=>.)
(<==>) = (.<=>.)
(⇔) = (.<=>.)
(↔) = (.<=>.)
infixl 2 .<=>., <=>, <==>, ⇔, ↔

-- | And/conjunction synonyms
(∧), (·) :: IsCombinable formula => formula -> formula -> formula
(∧) = (.&.)
(·) = (.&.)
infixl 5 .&., ∧, ·

-- | Or/disjunction synonyms
(∨) :: IsCombinable formula => formula -> formula -> formula
(∨) = (.|.)
infixl 4 .|., ∨

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

-- Testing the parser and printer.

{-
-- | Make sure associative operators are grouped left to right, use this
-- to make more equality tests succeed.
leftAssociate :: IsCombinable formula => formula -> formula
canonical fm =
    foldCombination dj cj imp iff other (canonical1 fm)
    where
      dj p q = foldCombination ho dj' cj' (canonical p) (canonical q)
-}

-- Template Haskell magic to build infix declarations using defined symbols.
-- (Does not seem to have any effect.)
$(pure [InfixD (Fixity notPrec InfixN) '(.~.),
        InfixD (Fixity notPrec InfixN) '(¬),
        InfixD (Fixity iffPrec InfixL) '(.<=>.),
        InfixD (Fixity iffPrec InfixL) '(.<~>.),
        InfixD (Fixity iffPrec InfixL) '(⇔),
        InfixD (Fixity iffPrec InfixL) '(<=>),
        InfixD (Fixity iffPrec InfixL) '(<==>),
        InfixD (Fixity impPrec InfixR) '(.=>.),
        InfixD (Fixity impPrec InfixR) '(⇒),
        InfixD (Fixity impPrec InfixR) '(==>),
        InfixD (Fixity orPrec InfixL) '(.|.),
        InfixD (Fixity orPrec InfixL) '(∨),
        InfixD (Fixity andPrec InfixL) '(.&.),
        InfixD (Fixity andPrec InfixL) '(∧)])
