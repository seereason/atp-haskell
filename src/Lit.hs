{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lit
    ( IsLiteral(foldLiteral)
    , zipLiterals
    , LFormula(T, F, Atom, Not)
    ) where

import Data.Monoid ((<>))
import Prelude hiding (negate, null)

import Formulas (HasBoolean(..), IsAtom, IsNegatable(..), IsFormula(atomic, overatoms, onatoms, prettyFormula))
import Pretty (Associativity(..), Fixity(..), HasFixity(fixity), Pretty(pPrint), rootFixity, Side(Unary), text)

-- | Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (IsFormula lit atom, IsNegatable lit, HasBoolean lit) => IsLiteral lit atom where
    foldLiteral :: (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r

-- | Unify two literals
zipLiterals :: IsLiteral lit atom =>
               (lit -> lit -> Maybe r)
            -> (Bool -> Bool -> Maybe r)
            -> (atom -> atom -> Maybe r)
            -> lit -> lit -> Maybe r
zipLiterals neg tf at fm1 fm2 =
    foldLiteral neg' tf' at' fm1
    where
      neg' p1 = foldLiteral (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

data LFormula atom
    = F
    | T
    | Atom atom
    | Not (LFormula atom)
    deriving (Eq, Ord, Read)

instance HasBoolean (LFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance HasFixity (LFormula atom) where
    fixity T = Fixity 10 InfixN
    fixity F = Fixity 10 InfixN
    fixity a@(Atom _) = fixity a
    fixity (Not _) = Fixity 5 InfixN

instance Ord atom => IsNegatable (LFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance IsAtom atom => IsFormula (LFormula atom) atom where
    atomic = Atom
    overatoms f fm b =
        case fm of
          Atom a -> f a b
          Not p -> overatoms f p b
          _ -> b
    onatoms f fm =
        case fm of
          Atom a -> f a
          Not p -> Not (onatoms f p)
          _ -> fm
    prettyFormula fix _ lit =
        foldLiteral ne tf at lit
        where
          ne p = text "¬" <> prettyFormula (fixity lit) Unary p
          tf = pPrint
          at a = pPrint a

instance IsAtom atom => Pretty (LFormula atom) where
    pPrint = prettyFormula rootFixity Unary

instance IsAtom atom => IsLiteral (LFormula atom) atom where
    foldLiteral ne tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not f -> ne f
