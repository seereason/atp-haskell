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

data Formula a
    = False'
    | True'
    | Atom a
    | Not (Formula a)
    | And (Formula a) (Formula a)
    | Or (Formula a) (Formula a)
    | Imp (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)
    | Forall V (Formula a)
    | Exists V (Formula a)
    deriving (Eq, Ord, Read)

instance Show a => Show (Formula a) where
    show False' = "false"
    show True' = "true"
    show (Atom a) = show a
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"
    show (Forall v f) = "(for_all " ++ show v ++ " " ++ show f ++ ")"
    show (Exists v f) = "(exists " ++ show v ++ " " ++ show f ++ ")"

-- Infix operators
(.|.) :: Formula a -> Formula a -> Formula a
a .|. b = Or a b

(.&.) :: Formula a -> Formula a -> Formula a
a .&. b = And a b

(.=>.) :: Formula a -> Formula a -> Formula a
a .=>. b = Imp a b

(.<=>.) :: Formula a -> Formula a -> Formula a
a .<=>. b = Iff a b

(.~.) :: Formula a -> Formula a
(.~.) a = Not a

true :: Formula a
true = True'

false :: Formula a
false = False'

atomic :: a -> Formula a
atomic = Atom

(==>) :: Formula a -> Formula a -> Formula a
(==>) = (.=>.)
(<=>) :: Formula a -> Formula a -> Formula a
(<=>) = (.<=>.)

(∧) :: Formula a -> Formula a -> Formula a
(∧) = (.&.)
(∨) :: Formula a -> Formula a -> Formula a
(∨) = (.|.)
-- | ⇒ can't be a function when -XUnicodeSyntax is enabled - it
-- becomes a special character used in type signatures.
(⇒) :: Formula a -> Formula a -> Formula a
(⇒) = (.=>.)
(⇔) :: Formula a -> Formula a -> Formula a
(⇔) = (.<=>.)
(¬) :: Formula a -> Formula a
(¬) = (.~.)
(⊨) :: Formula a
(⊨) = true
(⊭) :: Formula a
(⊭) = false

for_all :: V -> Formula a -> Formula a
for_all = Forall

exists :: V -> Formula a -> Formula a
exists = Exists

infixl 1  .<=>. , ⇔, <=>
infixr 2  .=>., ⇒, ==>
infixr 3  .|., ∨
infixl 4  .&., ∧

-- | Apply a function to the atoms, otherwise keeping structure.
onatoms :: (a -> Formula a) -> Formula a -> Formula a
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
overatoms :: (a -> r -> r) -> Formula a -> r -> r
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
atom_union :: Ord a => (t -> Set a) -> Formula t -> Set a
atom_union f fm = overatoms (\h t -> Set.union (f h) t) fm Set.empty
