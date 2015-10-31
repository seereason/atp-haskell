-- | 'IsLiteral' is a subclass of formulas that support negation and
-- have true and false elements.

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lit
    ( IsLiteral(foldLiteral'), foldLiteral
    , JustLiteral
    , onatomsLiteral
    , overatomsLiteral
    , zipLiterals', zipLiterals
    , convertLiteral
    , convertToLiteral
    , fixityLiteral
    , prettyLiteral
    , showLiteral
    , Literal
    , markLiteral
    , unmarkLiteral
#ifndef NOTESTS
    , LFormula(T, F, Atom, Not)
#endif
    ) where

import Data.Generics (Data)
import Data.Monoid ((<>))
import Formulas (HasBoolean(..), IsAtom, IsNegatable(..), IsFormula(atomic, AtomOf), (.~.))
import Lib (Marked(Mark, unMark'))
import Prelude hiding (negate, null)
import Pretty (Associativity(..), Doc, Expr, Fixity(..), HasFixity(fixity), markExpr, Pretty(pPrint), text)
#ifndef NOTESTS
import Formulas (overatoms, onatoms)
#endif

-- | Literals are the building blocks of the clause and implicative normal
-- forms.  They support negation and must include True and False elements.
class (IsFormula lit, IsNegatable lit, HasBoolean lit) => IsLiteral lit where
    -- | This is the internal fold for literals, 'foldLiteral' below should
    -- normally be used, but its argument must be an instance of 'JustLiteral'.
    foldLiteral' :: (lit -> r) -- ^ Called for higher order formulas (non-literal)
                 -> (lit -> r) -- ^ Called for negated formulas
                 -> (Bool -> r) -- ^ Called for true and false formulas
                 -> (AtomOf lit -> r) -- ^ Called for atomic formulas
                 -> lit -> r

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
convertToLiteral :: (IsLiteral formula, JustLiteral lit
                    ) => (formula -> lit) -> (AtomOf formula -> AtomOf lit) -> formula -> lit
convertToLiteral ho ca fm = foldLiteral' ho (\fm' -> (.~.) (convertToLiteral ho ca fm')) fromBool (atomic . ca) fm

fixityLiteral :: JustLiteral lit => lit -> Fixity
fixityLiteral fm =
    foldLiteral ne tf at fm
    where
      ne _ = Fixity 5 InfixA
      tf _ = Fixity 10 InfixN
      at = fixity

-- | Implementation of 'pPrint' for -- 'JustLiteral' types.
prettyLiteral :: JustLiteral lit => lit -> Doc
prettyLiteral lit =
    foldLiteral ne tf at lit
    where
      ne p = text "¬" <> prettyLiteral p
      tf = pPrint
      at a = pPrint a

showLiteral :: JustLiteral lit => lit -> String
showLiteral lit = foldLiteral ne tf at lit
    where
      ne p = "(.~.)(" ++ showLiteral p ++ ")"
      tf = show
      at = show

-- | Implementation of 'onatoms' for 'JustLiteral' types.
onatomsLiteral :: JustLiteral lit => (AtomOf lit -> lit) -> lit -> lit
onatomsLiteral f fm =
    foldLiteral ne tf at fm
    where
      ne p = onatomsLiteral f p
      tf flag = fromBool flag
      at x = f x

-- | implementation of 'overatoms' for 'JustLiteral' types.
overatomsLiteral :: JustLiteral lit => (AtomOf lit -> r -> r) -> lit -> r -> r
overatomsLiteral f fm r0 =
        foldLiteral ne (const r0) (flip f r0) fm
        where
          ne fm' = overatomsLiteral f fm' r0

-- | Type used as a parameter to 'Marked' to indicate Literal values.
data Literal
deriving instance Data Literal

-- We only want these simple instances for specific markings, not the
-- general Marked mk case.
instance Show formula => Show (Marked Literal formula) where
    show (Mark x) = "markLiteral (" ++ show x ++ ")"

instance Eq formula => Eq (Marked Literal formula) where
    Mark a == Mark b = a == b

instance Ord formula => Ord (Marked Literal formula)where
    compare (Mark a) (Mark b) = compare a b

instance Show (Marked Expr formula) => Show (Marked Expr (Marked Literal formula)) where
    show (Mark (Mark fm)) = "markLiteral (" ++ show (markExpr fm) ++ ")"

instance IsLiteral formula => JustLiteral (Marked Literal formula)

markLiteral :: IsLiteral lit => lit -> Marked Literal lit
markLiteral = Mark

unmarkLiteral :: IsLiteral pf => Marked Literal pf -> pf
unmarkLiteral = unMark'

instance (IsLiteral formula, IsNegatable formula) => IsLiteral (Marked mk formula) where
    foldLiteral' ho ne tf at (Mark x) = foldLiteral' (ho . Mark) (ne . Mark) tf at x

#ifndef NOTESTS
-- | Example of a 'JustLiteral' type.
data LFormula atom
    = F
    | T
    | Atom atom
    | Not (LFormula atom)
    deriving (Eq, Ord, Read, Show)

instance IsAtom atom => IsFormula (LFormula atom) where
    type AtomOf (LFormula atom) = atom
    atomic = Atom
    overatoms = overatomsLiteral
    onatoms = onatomsLiteral

instance (IsFormula (LFormula atom), Eq atom, Ord atom) => IsLiteral (LFormula atom) where
    foldLiteral' _ ne tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not f -> ne f

instance IsAtom atom => JustLiteral (LFormula atom)

instance HasBoolean (LFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance Ord atom => IsNegatable (LFormula atom) where
    naiveNegate = Not
    foldNegation' inverted normal (Not x) = foldNegation' normal inverted x
    foldNegation' _ normal x = normal x

instance IsAtom atom => HasFixity (LFormula atom) where
    fixity = fixityLiteral

instance IsAtom atom => Pretty (LFormula atom) where
    pPrint = prettyLiteral
#endif
