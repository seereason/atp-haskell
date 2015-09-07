-- | Polymorphic type of formulas
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall #-}
module Formulas
    ( -- * True and False
      Constants(asBool, fromBool), prettyBool
    , true, false, (⊨), (⊭)
    -- * Negation
    , Negatable((.~.), foldNegation), (¬), negate, negated, negative, positive
    -- * Combinable
    , Combinable((.|.), (.&.), (.<=>.), (.=>.), (.<=.), (.<~>.), (.~|.), (.~&.))
    , (==>), (<=>), (∧), (∨), (⇒), (⇔)
    , Combination(..), BinOp(..), combine, binop
    -- * Variables
    , Variable(variant, prefix, prettyVariable), variants, showVariable, V(V)
    -- * Quantifiers
    , Quant((:!:), (:?:))
    -- * Formulas
    , Formulae(atomic, foldAtoms, mapAtoms)
    , Formula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    , onatoms
    , overatoms
    , atom_union
    ) where

import Data.Data (Data)
import Data.Monoid ((<>))
import Data.Set as Set (Set, empty, insert, member, union)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixL, InfixR, InfixN))
import Lib.Pretty (HasFixity(fixity), topFixity)
import Prelude hiding (negate)
import Text.PrettyPrint.HughesPJClass (Doc, Pretty(pPrint), text)

-- |Types that need to have True and False elements.
class Constants p where
    asBool :: p -> Maybe Bool
    fromBool :: Bool -> p

true :: Constants p => p
true = fromBool True

false :: Constants p => p
false = fromBool False

(⊨) :: Constants p => p
(⊨) = true

(⊭) :: Constants p => p
(⊭) = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊨"
prettyBool False = text "⊭"

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'Literal' class.
class Negatable formula where
    -- | Negate a formula
    (.~.) :: formula -> formula
    -- | Test whether a formula is negated or normal
    foldNegation :: (formula -> r) -- ^ called for normal formulas
                 -> (formula -> r) -- ^ called for negated formulas
                 -> formula -> r
-- | Is this formula negated at the top level?
negated :: Negatable formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

(¬) :: Negatable formula => formula -> formula
(¬) = (.~.)

negate :: Negatable formula => formula -> formula
negate = (.~.)

-- | Some operations on Negatable formulas
negative :: Negatable formula => formula -> Bool
negative = negated

positive :: Negatable formula => formula -> Bool
positive = not . negative

infix 5 .~., ¬

-- | A type class for combining logical formulas.  Minimal implementation:
-- @
--  (.|.)
-- @
class (Negatable formula) => Combinable formula where
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

(==>) :: Combinable formula => formula -> formula -> formula
(==>) = (.=>.)
(<=>) :: Combinable formula => formula -> formula -> formula
(<=>) = (.<=>.)

(∧) :: Combinable formula => formula -> formula -> formula
(∧) = (.&.)
(∨) :: Combinable formula => formula -> formula -> formula
(∨) = (.|.)

-- | ⇒ can't be a function when -XUnicodeSyntax is enabled - it
-- becomes a special character used in type signatures.
(⇒) :: Combinable formula => formula -> formula -> formula
(⇒) = (.=>.)
(⇔) :: Combinable formula => formula -> formula -> formula
(⇔) = (.<=>.)

-- |The 'Combination' and 'BinOp' types can either be used as helper
-- types for writing folds, or they can be embedded in a concrete type
-- intended to be a Combinable instance.
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
combine :: Combinable formula => Combination formula -> formula
combine (BinOp f1 (:<=>:) f2) = f1 .<=>. f2
combine (BinOp f1 (:=>:) f2) = f1 .=>. f2
combine (BinOp f1 (:&:) f2) = f1 .&. f2
combine (BinOp f1 (:|:) f2) = f1 .|. f2
combine ((:~:) f) = (.~.) f

binop :: Combinable formula => formula -> BinOp -> formula -> formula
binop a (:&:) b = a .&. b
binop a (:|:) b = a .|. b
binop a (:=>:) b = a .=>. b
binop a (:<=>:) b = a .<=>. b

class (Ord v, IsString v, Data v, Pretty v) => Variable v where
    variant :: v -> Set.Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.
    prettyVariable :: v -> Doc
    -- ^ Pretty print a variable

-- | Return an infinite list of variations on v
variants :: Variable v => v -> [v]
variants v0 =
    iter' Set.empty v0
    where iter' s v = let v' = variant v s in v' : iter' (Set.insert v s) v'

showVariable :: Variable v => v -> String
showVariable v = "(fromString (" ++ show (show (prettyVariable v)) ++ "))"

newtype V = V String deriving (Eq, Ord, Read, Data, Typeable)

instance Variable V where
    variant v@(V s) vs = if Set.member v vs then variant (V (s ++ "'")) vs else v
    prefix pre (V s) = V (pre ++ s)
    prettyVariable (V s) = text s

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pPrint (V s) = text s

data Quant
    = (:!:) -- ^ for_all
    | (:?:) -- ^ exists
    deriving (Eq, Ord, Data, Typeable)

data Formula atom
    = F
    | T
    | Atom atom
    | Not (Formula atom)
    | And (Formula atom) (Formula atom)
    | Or (Formula atom) (Formula atom)
    | Imp (Formula atom) (Formula atom)
    | Iff (Formula atom) (Formula atom)
    | Forall V (Formula atom)
    | Exists V (Formula atom)
    deriving (Eq, Ord, Read)

instance Constants (Formula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance Negatable (Formula atom) where
    (.~.) = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Combinable (Formula atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff

-- | Class associating a formula type with its atom type.
class Formulae formula atom | formula -> atom where
    atomic :: atom -> formula
    -- ^ Build a formula from an atom.
    foldAtoms :: (atom -> r -> r) -> formula -> r -> r
    -- ^ Formula analog of list iterator "itlist".
    mapAtoms :: (atom -> formula) -> formula -> formula
    -- ^ Apply a function to the atoms, otherwise keeping structure.

-- infixr 9 !, ?, ∀, ∃

-- Display formulas using infix notation
instance Show atom => Show (Formula atom) where
    show F = "false"
    show T = "true"
    show (Atom atom) = "atomic (" ++ show atom ++ ")"
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"
    show (Forall v f) = "(for_all " ++ show v ++ " " ++ show f ++ ")"
    show (Exists v f) = "(exists " ++ show v ++ " " ++ show f ++ ")"

instance HasFixity atom => HasFixity (Formula atom) where
    fixity T = Fixity 10 InfixN
    fixity F = Fixity 10 InfixN
    fixity (Atom a) = fixity a
    fixity (Not _) = Fixity 5 InfixN
    fixity (And _ _) = Fixity 4 InfixL
    fixity (Or _ _) = Fixity 3 InfixL
    fixity (Imp _ _) = Fixity 2 InfixR
    fixity (Iff _ _) = Fixity 1 InfixL
    fixity (Forall _ _) = Fixity 9 InfixN
    fixity (Exists _ _) = Fixity 9 InfixN

-- | Show a formula in a visually pleasing format.
prettyFormula :: HasFixity atom =>
                 (atom -> Doc)
              -> Fixity        -- ^ The fixity of the parent formula.  If the operator being formatted here
                               -- has a lower precedence it needs to be parenthesized.
              -> Formula atom
              -> Doc
prettyFormula prettyAtom (Fixity parentPrecidence parentDirection) fm =
    parenIf (parentPrecidence > precidence) (pp fm)
    where
      fix@(Fixity precidence direction) = fixity fm
      parenIf True x = text "(" <> x <> text ")"
      parenIf False x = x
      pp F = text "⊨"
      pp T = text "⊭"
      pp (Atom atom) = prettyAtom atom
      pp (Not f) = text "¬" <> prettyFormula prettyAtom fix f
      pp (And f g) = prettyFormula prettyAtom fix f <> text "∧" <> prettyFormula prettyAtom fix g
      pp (Or f g) = prettyFormula prettyAtom fix f <> text "∨" <> prettyFormula prettyAtom fix g
      pp (Imp f g) = prettyFormula prettyAtom fix f <> text "⇒" <> prettyFormula prettyAtom fix g
      pp (Iff f g) = prettyFormula prettyAtom fix f <> text "⇔" <> prettyFormula prettyAtom fix g
      pp (Forall v f) = text ("∀" ++ show v ++ ". ") <> prettyFormula prettyAtom fix f
      pp (Exists v f) = text ("∃" ++ show v ++ ". ") <> prettyFormula prettyAtom fix f

instance (HasFixity atom, Pretty atom)  => Pretty (Formula atom) where
    pPrint fm = prettyFormula pPrint topFixity fm

instance Formulae (Formula atom) atom where
    atomic = Atom
    foldAtoms f fm b =
      case fm of
        Atom a -> f a b
        Not p -> foldAtoms f p b
        And p q -> foldAtoms f p (foldAtoms f q b)
        Or p q -> foldAtoms f p (foldAtoms f q b)
        Imp p q -> foldAtoms f p (foldAtoms f q b)
        Iff p q -> foldAtoms f p (foldAtoms f q b)
        Forall _x p -> foldAtoms f p b
        Exists _x p -> foldAtoms f p b
        _ -> b
    mapAtoms f fm =
      case fm of
        Atom a -> f a
        Not p -> Not (mapAtoms f p)
        And p q -> And (mapAtoms f p) (mapAtoms f q)
        Or p q -> Or (mapAtoms f p) (mapAtoms f q)
        Imp p q -> Imp (mapAtoms f p) (mapAtoms f q)
        Iff p q -> Iff (mapAtoms f p) (mapAtoms f q)
        Forall x p -> Forall x (mapAtoms f p)
        Exists x p -> Exists x (mapAtoms f p)
        _ -> fm

overatoms :: Formulae formula atom => (atom -> r -> r) -> formula -> r -> r
overatoms = foldAtoms
onatoms :: Formulae formula atom => (atom -> formula) -> formula -> formula
onatoms = mapAtoms

-- | Special case of a union of the results of a function over the atoms.
atom_union :: (Formulae formula atom, Ord r) => (atom -> Set r) -> formula -> Set r
atom_union f fm = foldAtoms (\h t -> Set.union (f h) t) fm Set.empty
