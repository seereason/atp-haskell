-- | 'IsLiteral' is a subclass of formulas that support negation and
-- have true and false elements.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lit
    ( IsLiteral(foldLiteral'), foldLiteral
    , JustLiteral
    , onatomsLiteral
    , overatomsLiteral
    , zipLiterals', zipLiterals
    , convertLiteral
    , convertToLiteral
    , prettyLiteral
    , LFormula(T, F, Atom, Not)
    ) where

import Data.Monoid ((<>))
import Prelude hiding (negate, null)

import Formulas (HasBoolean(..), IsNegatable(..), IsFormula(atomic, overatoms, onatoms), (.~.))
import Pretty (Associativity(..), Doc, Fixity(..), HasFixity(fixity), Pretty(pPrint), text)

-- | Literals are the building blocks of the clause and implicative normal
-- forms.  They support negation and must include True and False elements.
class (IsFormula lit atom,
       IsNegatable lit,
       HasBoolean lit,
       Pretty atom, -- We will definitely want to render these
       Ord atom -- atoms almost always end up in sets, so this is indispensable
      ) => IsLiteral lit atom where
    foldLiteral' :: (lit -> r) -> (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r

foldLiteral :: IsLiteral lit atom => (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r
foldLiteral = foldLiteral' (error "JustLiteral failure")

-- | Class that indicates that a formula type *only* supports Literal
-- features - no combinations or quantifiers.
class JustLiteral formula

-- | Unify two literals
zipLiterals' :: (IsLiteral lit1 atom1, IsLiteral lit2 atom2) =>
                (lit1 -> lit2 -> Maybe r)
             -> (lit1 -> lit2 -> Maybe r)
             -> (Bool -> Bool -> Maybe r)
             -> (atom1 -> atom2 -> Maybe r)
             -> lit1 -> lit2 -> Maybe r
zipLiterals' ho neg tf at fm1 fm2 =
    foldLiteral' ho' neg' tf' at' fm1
    where
      ho' x1 = foldLiteral' (ho x1) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      neg' p1 = foldLiteral' (\ _ -> Nothing) (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral' (\ _ -> Nothing) (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral' (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

zipLiterals :: (IsLiteral lit1 atom1, JustLiteral lit1, IsLiteral lit2 atom2, JustLiteral lit2) =>
               (lit1 -> lit2 -> Maybe r)
            -> (Bool -> Bool -> Maybe r)
            -> (atom1 -> atom2 -> Maybe r)
            -> lit1 -> lit2 -> Maybe r
zipLiterals neg tf at fm1 fm2 =
    foldLiteral neg' tf' at' fm1
    where
      neg' p1 = foldLiteral (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

-- | Convert a 'JustLiteral' instance to any 'IsLiteral' instance.
convertLiteral :: (IsLiteral lit1 atom1, JustLiteral lit1, IsLiteral lit2 atom2) => (atom1 -> atom2) -> lit1 -> lit2
convertLiteral ca fm = foldLiteral (\fm' -> (.~.) (convertLiteral ca fm')) fromBool (atomic . ca) fm

-- | Convert any formula to a literal, passing non-IsLiteral
-- structures to the first argument (typically a call to error.)
convertToLiteral :: (IsLiteral formula atom1, IsLiteral lit atom2, JustLiteral lit
                    ) => (formula -> lit) -> (atom1 -> atom2) -> formula -> lit
convertToLiteral ho ca fm = foldLiteral' ho (\fm' -> (.~.) (convertToLiteral ho ca fm')) fromBool (atomic . ca) fm

fixityLiteral :: (IsLiteral lit atom, JustLiteral lit, HasFixity atom) => lit -> Fixity
fixityLiteral fm =
    foldLiteral ne tf at fm
    where
      ne _ = Fixity 5 InfixN
      tf _ = Fixity 10 InfixN
      at = fixity

-- | Function typically used to implement Pretty instances for
-- JustLiteral formulas.
prettyLiteral :: (IsLiteral formula atom, JustLiteral formula) => formula -> Doc
prettyLiteral lit =
    foldLiteral ne tf at lit
    where
      ne p = text "¬" <> prettyLiteral p
      tf = pPrint
      at a = pPrint a

#ifndef NOTESTS
data LFormula atom
    = F
    | T
    | Atom atom
    | Not (LFormula atom)
    deriving (Eq, Ord, Read)

instance JustLiteral (LFormula atom)

instance HasBoolean (LFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance (Ord atom, Pretty atom, HasFixity atom) => HasFixity (LFormula atom) where
    fixity = fixityLiteral

instance Ord atom => IsNegatable (LFormula atom) where
    naiveNegate = Not
    foldNegation' inverted normal (Not x) = foldNegation' normal inverted x
    foldNegation' _ normal x = normal x

-- | Apply a function to the atoms, otherwise keeping structure.  This
-- can generally be used as the onatoms method of IsFormula.
onatomsLiteral :: forall lit atom. IsLiteral lit atom => (atom -> lit) -> lit -> lit
onatomsLiteral f fm =
    foldLiteral ne tf at fm
    where
      ne p = onatomsLiteral f p
      tf flag = fromBool flag
      at x = f x

-- | Formula analog of list iterator "itlist".
overatomsLiteral :: forall lit atom r. (IsLiteral lit atom, JustLiteral lit) => (atom -> r -> r) -> lit -> r -> r
overatomsLiteral f fm r0 =
        foldLiteral ne (const r0) (flip f r0) fm
        where
          ne fm' = overatomsLiteral f fm' r0

instance (Ord atom, Pretty atom) => IsFormula (LFormula atom) atom where
    atomic = Atom
    overatoms = overatomsLiteral
    onatoms = onatomsLiteral

instance (Ord atom, Pretty atom) => Pretty (LFormula atom) where
    pPrint = prettyLiteral

instance (Ord atom, Pretty atom) => IsLiteral (LFormula atom) atom where
    foldLiteral' _ ne tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not f -> ne f
#endif
