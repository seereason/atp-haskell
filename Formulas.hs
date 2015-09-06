{-# OPTIONS_GHC -Wall #-}
module Formulas
    ( V(V), Formula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    , (.|.), (.&.), (.=>.), (.<=>.), (.~.), true, false, atomic
    , (==>), (<=>), (∧), (∨), (⇒), (⇔), (¬), (⊨), (⊭)
    , for_all, exists
    , onatoms
    , overatoms
    , atom_union
    ) where

import Data.Monoid ((<>))
import Data.Set as Set (Set, empty, union)
import Data.String (IsString(fromString))
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixL, InfixR, InfixN))
import Lib.Pretty (HasFixity(fixity), topFixity)
import Text.PrettyPrint.HughesPJClass (Doc, Pretty(pPrint), text)

newtype V = V String deriving (Eq, Ord, Read)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pPrint (V s) = text s

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

-- Infix operators
(.|.) :: Formula atom -> Formula atom -> Formula atom
a .|. b = Or a b

(.&.) :: Formula atom -> Formula atom -> Formula atom
a .&. b = And a b

(.=>.) :: Formula atom -> Formula atom -> Formula atom
a .=>. b = Imp a b

(.<=>.) :: Formula atom -> Formula atom -> Formula atom
a .<=>. b = Iff a b

(.~.) :: Formula atom -> Formula atom
(.~.) a = Not a

true :: Formula atom
true = T

false :: Formula atom
false = F

atomic :: atom -> Formula atom
atomic = Atom

(==>) :: Formula atom -> Formula atom -> Formula atom
(==>) = (.=>.)
(<=>) :: Formula atom -> Formula atom -> Formula atom
(<=>) = (.<=>.)

(∧) :: Formula atom -> Formula atom -> Formula atom
(∧) = (.&.)
(∨) :: Formula atom -> Formula atom -> Formula atom
(∨) = (.|.)
-- | ⇒ can't be a function when -XUnicodeSyntax is enabled - it
-- becomes a special character used in type signatures.
(⇒) :: Formula atom -> Formula atom -> Formula atom
(⇒) = (.=>.)
(⇔) :: Formula atom -> Formula atom -> Formula atom
(⇔) = (.<=>.)
(¬) :: Formula atom -> Formula atom
(¬) = (.~.)
(⊨) :: Formula atom
(⊨) = true
(⊭) :: Formula atom
(⊭) = false

for_all :: V -> Formula atom -> Formula atom
for_all = Forall

exists :: V -> Formula atom -> Formula atom
exists = Exists

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

infixl 1  .<=>. , ⇔, <=>
infixr 2  .=>., ⇒, ==>
infixr 3  .|., ∨
infixl 4  .&., ∧
-- infixr 9 !, ?, ∀, ∃

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

-- | Apply a function to the atoms, otherwise keeping structure.
onatoms :: (atom -> Formula atom) -> Formula atom -> Formula atom
onatoms f fm =
    case fm of
      Atom a -> f a
      Not p -> Not (onatoms f p)
      And p q -> And (onatoms f p) (onatoms f q)
      Or p q -> Or (onatoms f p) (onatoms f q)
      Imp p q -> Imp (onatoms f p) (onatoms f q)
      Iff p q -> Iff (onatoms f p) (onatoms f q)
      Forall x p -> Forall x (onatoms f p)
      Exists x p -> Exists x (onatoms f p)
      _ -> fm

-- | Formula analog of list iterator "itlist".
overatoms :: (atom -> r -> r) -> Formula atom -> r -> r
overatoms f fm b =
  case fm of
    Atom a -> f a b
    Not p -> overatoms f p b
    And p q -> overatoms f p (overatoms f q b)
    Or p q -> overatoms f p (overatoms f q b)
    Imp p q -> overatoms f p (overatoms f q b)
    Iff p q -> overatoms f p (overatoms f q b)
    Forall _x p -> overatoms f p b
    Exists _x p -> overatoms f p b
    _ -> b

-- | Special case of a union of the results of a function over the atoms.
atom_union :: Ord a => (atom -> Set a) -> Formula atom -> Set a
atom_union f fm = overatoms (\h t -> Set.union (f h) t) fm Set.empty
