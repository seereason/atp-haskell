-- | 'IsLiteral' is a subclass of formulas that support negation and
-- have true and false elements.

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.Lit
    ( IsLiteral(naiveNegate, foldNegation, foldLiteral')
    , (.~.), (¬), negate
    , negated
    , negative, positive
    , foldLiteral
    , JustLiteral
    , onatomsLiteral
    , overatomsLiteral
    , zipLiterals', zipLiterals
    , convertLiteral
    , convertToLiteral
    , precedenceLiteral
    , associativityLiteral
    , prettyLiteral
    , showLiteral
    -- * Instance
    , LFormula(T, F, Atom, Not)
    , Lit(L, lname)
    ) where

import Data.Data (Data)
import Data.Logic.ATP.Formulas (IsAtom, IsFormula(atomic, AtomOf, asBool, false, true), fromBool, overatoms, onatoms, prettyBool)
import Data.Logic.ATP.Pretty (Associativity(..), boolPrec, Doc, HasFixity(precedence, associativity), notPrec, Precedence, text)
import Data.Monoid ((<>))
import Data.Typeable (Typeable)
import Prelude hiding (negate, null)
import Text.PrettyPrint.HughesPJClass (maybeParens, Pretty(pPrint, pPrintPrec), PrettyLevel, prettyNormal)

-- | The class of formulas that can be negated.  Literals are the
-- building blocks of the clause and implicative normal forms.  They
-- support negation and must include true and false elements.
class IsFormula lit => IsLiteral lit where
    -- | Negate a formula in a naive fashion, the operators below
    -- prevent double negation.
    naiveNegate :: lit -> lit
    -- | Test whether a lit is negated or normal
    foldNegation :: (lit -> r) -- ^ called for normal formulas
                 -> (lit -> r) -- ^ called for negated formulas
                 -> lit -> r
    -- | This is the internal fold for literals, 'foldLiteral' below should
    -- normally be used, but its argument must be an instance of 'JustLiteral'.
    foldLiteral' :: (lit -> r) -- ^ Called for higher order formulas (non-literal)
                 -> (lit -> r) -- ^ Called for negated formulas
                 -> (Bool -> r) -- ^ Called for true and false formulas
                 -> (AtomOf lit -> r) -- ^ Called for atomic formulas
                 -> lit -> r

-- | Is this formula negated at the top level?
negated :: IsLiteral formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

-- | Negate the formula, avoiding double negation
(.~.), (¬), negate :: IsLiteral formula => formula -> formula
(.~.) = foldNegation naiveNegate id
(¬) = (.~.)
negate = (.~.)
infix 6 .~., ¬

-- | Some operations on IsLiteral formulas
negative :: IsLiteral formula => formula -> Bool
negative = negated

positive :: IsLiteral formula => formula -> Bool
positive = not . negative

foldLiteral :: JustLiteral lit => (lit -> r) -> (Bool -> r) -> (AtomOf lit -> r) -> lit -> r
foldLiteral = foldLiteral' (error "JustLiteral failure")

-- | Class that indicates that a formula type *only* contains 'IsLiteral'
-- features - no combinations or quantifiers.
class IsLiteral formula => JustLiteral formula

-- | Combine two literals (internal version).
zipLiterals' :: (IsLiteral lit1, IsLiteral lit2) =>
                (lit1 -> lit2 -> Maybe r)
             -> (lit1 -> lit2 -> Maybe r)
             -> (Bool -> Bool -> Maybe r)
             -> (AtomOf lit1 -> AtomOf lit2 -> Maybe r)
             -> lit1 -> lit2 -> Maybe r
zipLiterals' ho neg tf at fm1 fm2 =
    foldLiteral' ho' neg' tf' at' fm1
    where
      ho' x1 = foldLiteral' (ho x1) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      neg' p1 = foldLiteral' (\ _ -> Nothing) (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral' (\ _ -> Nothing) (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral' (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

-- | Combine two literals.
zipLiterals :: (JustLiteral lit1, JustLiteral lit2) =>
               (lit1 -> lit2 -> Maybe r)
            -> (Bool -> Bool -> Maybe r)
            -> (AtomOf lit1 -> AtomOf lit2 -> Maybe r)
            -> lit1 -> lit2 -> Maybe r
zipLiterals neg tf at fm1 fm2 =
    foldLiteral neg' tf' at' fm1
    where
      neg' p1 = foldLiteral (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

-- | Convert a 'JustLiteral' instance to any 'IsLiteral' instance.
convertLiteral :: (JustLiteral lit1, IsLiteral lit2) => (AtomOf lit1 -> AtomOf lit2) -> lit1 -> lit2
convertLiteral ca fm = foldLiteral (\fm' -> (.~.) (convertLiteral ca fm')) fromBool (atomic . ca) fm

-- | Convert any formula to a literal, passing non-IsLiteral
-- structures to the first argument (typically a call to error.)
convertToLiteral :: (IsLiteral formula, JustLiteral lit) =>
                    (formula -> lit) -> (AtomOf formula -> AtomOf lit) -> formula -> lit
convertToLiteral ho ca fm = foldLiteral' ho (\fm' -> (.~.) (convertToLiteral ho ca fm')) fromBool (atomic . ca) fm

precedenceLiteral :: JustLiteral lit => lit -> Precedence
precedenceLiteral = foldLiteral (const notPrec) (const boolPrec) precedence
associativityLiteral :: JustLiteral lit => lit -> Associativity
associativityLiteral = foldLiteral (const InfixA) (const InfixN) associativity

-- | Implementation of 'pPrint' for -- 'JustLiteral' types.
prettyLiteral :: JustLiteral lit => PrettyLevel -> Rational -> lit -> Doc
prettyLiteral l r lit =
    maybeParens (l > prettyNormal || r > precedence lit) (foldLiteral ne tf at lit)
    where
      ne p = text "¬" <> prettyLiteral l (precedence lit) p
      tf = prettyBool
      at a = pPrint a

showLiteral :: JustLiteral lit => lit -> String
showLiteral lit = foldLiteral ne tf at lit
    where
      ne p = "(.~.)(" ++ showLiteral p ++ ")"
      tf = show
      at = show

-- | Implementation of 'onatoms' for 'JustLiteral' types.
onatomsLiteral :: JustLiteral lit => (AtomOf lit -> AtomOf lit) -> lit -> lit
onatomsLiteral f fm =
    foldLiteral ne tf at fm
    where
      ne p = (.~.) (onatomsLiteral f p)
      tf = fromBool
      at x = atomic (f x)

-- | implementation of 'overatoms' for 'JustLiteral' types.
overatomsLiteral :: JustLiteral lit => (AtomOf lit -> r -> r) -> lit -> r -> r
overatomsLiteral f fm r0 =
        foldLiteral ne (const r0) (flip f r0) fm
        where
          ne fm' = overatomsLiteral f fm' r0

-- | Example of a 'JustLiteral' type.
data LFormula atom
    = F
    | T
    | Atom atom
    | Not (LFormula atom)
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data Lit = L {lname :: String} deriving (Eq, Ord)

instance IsAtom atom => IsFormula (LFormula atom) where
    type AtomOf (LFormula atom) = atom
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    true = T
    false = F
    atomic = Atom
    overatoms = overatomsLiteral
    onatoms = onatomsLiteral

instance (IsFormula (LFormula atom), Eq atom, Ord atom) => IsLiteral (LFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x
    foldLiteral' _ ne tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not f -> ne f

instance IsAtom atom => JustLiteral (LFormula atom)

instance IsAtom atom => HasFixity (LFormula atom) where
    precedence = precedenceLiteral
    associativity = associativityLiteral

instance IsAtom atom => Pretty (LFormula atom) where
    pPrintPrec = prettyLiteral
