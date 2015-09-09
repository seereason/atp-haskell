-- | Polymorphic type of formulas
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
module Formulas
    ( -- * True and False
      HasBoolean(asBool, fromBool), prettyBool
    , true, false, (⊨), (⊭)
    -- * Negation
    , IsNegatable(naiveNegate, foldNegation), (.~.), (¬), negate, negated, negative, positive
    -- * IsCombinable
    , IsCombinable((.|.), (.&.), (.<=>.), (.=>.), (.<=.), (.<~>.), (.~|.), (.~&.))
    , (==>), (<=>), (∧), (∨), (⇒), (⇔)
    , Combination(..), BinOp(..), combine, binop
    -- * Formulas
    , IsFormula(atomic, foldAtoms, mapAtoms)
    , PFormula(F, T, Atom, Not, And, Or, Imp, Iff)
    , onatoms
    , overatoms
    , atom_union
    ) where

import Data.Data (Data)
import Data.Set as Set (Set, empty, union)
import Data.Typeable (Typeable)
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixL, InfixR, InfixN))
import Pretty (HasFixity(fixity))
import Prelude hiding (negate)
import Text.PrettyPrint.HughesPJClass (Doc, text)

-- |Types that need to have True and False elements.
class HasBoolean p where
    asBool :: p -> Maybe Bool
    fromBool :: Bool -> p

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

-- | Is this formula negated at the top level?
negated :: IsNegatable formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

-- | Negate the formula, avoiding double negation
(.~.) :: IsNegatable formula => formula -> formula
(.~.) = foldNegation naiveNegate id

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

    -- | Derived formula combinators.  These could (and should!) be
    -- overridden with expressions native to the instance.
    --
    -- | Conjunction/AND
    (.&.) :: formula -> formula -> formula
    x .&. y = (.~.) ((.~.) x .|. (.~.) y)
    -- | Formula combinators: Equivalence
    (.<=>.) :: formula -> formula -> formula
    x .<=>. y = (x .=>. y) .&. (y .=>. x)
    -- | Implication
    (.=>.) :: formula -> formula -> formula
    x .=>. y = ((.~.) x .|. y)
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
infixr 3  .|., ∨
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

-- |The 'Combination' and 'BinOp' types can either be used as helper
-- types for writing folds, or they can be embedded in a concrete type
-- intended to be a IsCombinable instance.
data Combination formula
    = BinOp formula BinOp formula
    | (:~:) formula
    deriving (Eq, Ord, Data, Typeable)

-- | Represents the boolean logic binary operations, used in the
-- Combination type above.
data BinOp
    = (:<=>:)  -- ^ Equivalence
    |  (:=>:)  -- ^ Implication
    |  (:&:)  -- ^ AND
    |  (:|:)  -- ^ OR
    deriving (Eq, Ord, Data, Typeable, Enum, Bounded)

-- | A helper function for building folds:
-- @
--   foldPropositional combine atomic
-- @
-- is a no-op.
combine :: IsCombinable formula => Combination formula -> formula
combine (BinOp f1 (:<=>:) f2) = f1 .<=>. f2
combine (BinOp f1 (:=>:) f2) = f1 .=>. f2
combine (BinOp f1 (:&:) f2) = f1 .&. f2
combine (BinOp f1 (:|:) f2) = f1 .|. f2
combine ((:~:) f) = (.~.) f

binop :: IsCombinable formula => formula -> BinOp -> formula -> formula
binop a (:&:) b = a .&. b
binop a (:|:) b = a .|. b
binop a (:=>:) b = a .=>. b
binop a (:<=>:) b = a .<=>. b

data PFormula atom
    = F
    | T
    | Atom atom
    | Not (PFormula atom)
    | And (PFormula atom) (PFormula atom)
    | Or (PFormula atom) (PFormula atom)
    | Imp (PFormula atom) (PFormula atom)
    | Iff (PFormula atom) (PFormula atom)
    deriving (Eq, Ord, Read)

instance HasBoolean (PFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance IsNegatable (PFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance IsCombinable (PFormula atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff

-- | Class associating a formula type with its atom type.
class IsFormula formula atom | formula -> atom where
    atomic :: atom -> formula
    -- ^ Build a formula from an atom.
    foldAtoms :: (atom -> r -> r) -> formula -> r -> r
    -- ^ Formula analog of list iterator "itlist".
    mapAtoms :: (atom -> formula) -> formula -> formula
    -- ^ Apply a function to the atoms, otherwise keeping structure.

-- infixr 9 !, ?, ∀, ∃

-- Display formulas using infix notation
instance Show atom => Show (PFormula atom) where
    show F = "false"
    show T = "true"
    show (Atom atom) = "atomic (" ++ show atom ++ ")"
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"

instance HasFixity atom => HasFixity (PFormula atom) where
    fixity T = Fixity 10 InfixN
    fixity F = Fixity 10 InfixN
    fixity (Atom a) = fixity a
    fixity (Not _) = Fixity 5 InfixN
    fixity (And _ _) = Fixity 4 InfixL
    fixity (Or _ _) = Fixity 3 InfixL
    fixity (Imp _ _) = Fixity 2 InfixR
    fixity (Iff _ _) = Fixity 1 InfixL

instance IsFormula (PFormula atom) atom where
    atomic = Atom
    foldAtoms f fm b =
      case fm of
        Atom a -> f a b
        Not p -> foldAtoms f p b
        And p q -> foldAtoms f p (foldAtoms f q b)
        Or p q -> foldAtoms f p (foldAtoms f q b)
        Imp p q -> foldAtoms f p (foldAtoms f q b)
        Iff p q -> foldAtoms f p (foldAtoms f q b)
        _ -> b
    mapAtoms f fm =
      case fm of
        Atom a -> f a
        Not p -> Not (mapAtoms f p)
        And p q -> And (mapAtoms f p) (mapAtoms f q)
        Or p q -> Or (mapAtoms f p) (mapAtoms f q)
        Imp p q -> Imp (mapAtoms f p) (mapAtoms f q)
        Iff p q -> Iff (mapAtoms f p) (mapAtoms f q)
        _ -> fm

overatoms :: IsFormula formula atom => (atom -> r -> r) -> formula -> r -> r
overatoms = foldAtoms
onatoms :: IsFormula formula atom => (atom -> formula) -> formula -> formula
onatoms = mapAtoms

-- | Special case of a union of the results of a function over the atoms.
atom_union :: (IsFormula formula atom, Ord r) => (atom -> Set r) -> formula -> Set r
atom_union f fm = foldAtoms (\h t -> Set.union (f h) t) fm Set.empty
