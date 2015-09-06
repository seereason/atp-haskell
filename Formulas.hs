{-# OPTIONS_GHC -Wall #-}
module Formulas
    ( V(V), Formula(False', True', Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    , (.|.), (.&.), (.=>.), (.<=>.), (.~.), true, false, atomic
    , (==>), (<=>), (∧), (∨), (⇒), (⇔), (¬), (⊨), (⊭)
    , for_all, exists
    , onatoms
    , overatoms
    , atom_union
    ) where

import Data.Set as Set (Set, empty, union)
import Data.String (IsString(fromString))

newtype V = V String deriving (Eq, Ord, Read, Show)

instance IsString V where
    fromString = V

data Formula atom
    = False'
    | True'
    | Atom atom
    | Not (Formula atom)
    | And (Formula atom) (Formula atom)
    | Or (Formula atom) (Formula atom)
    | Imp (Formula atom) (Formula atom)
    | Iff (Formula atom) (Formula atom)
    | Forall V (Formula atom)
    | Exists V (Formula atom)
    deriving (Eq, Ord, Read)

instance Show atom => Show (Formula atom) where
    show False' = "false"
    show True' = "true"
    show (Atom atom) = "atomic (" ++ show atom ++ ")"
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"
    show (Forall v f) = "(for_all " ++ show v ++ " " ++ show f ++ ")"
    show (Exists v f) = "(exists " ++ show v ++ " " ++ show f ++ ")"

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
true = True'

false :: Formula atom
false = False'

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

infixl 1  .<=>. , ⇔, <=>
infixr 2  .=>., ⇒, ==>
infixr 3  .|., ∨
infixl 4  .&., ∧

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
