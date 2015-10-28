-- | 'IsLiteral' is a subclass of formulas that support negation and
-- have true and false elements.

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
#ifndef NOTESTS
    , LFormula(T, F, Atom, Not)
#endif
    ) where

import Data.Monoid ((<>))
import Formulas (HasBoolean(..), IsNegatable(..), IsFormula(atomic), (.~.))
import Prelude hiding (negate, null)
import Pretty (Associativity(..), Doc, Fixity(..), HasFixity(fixity), Pretty(pPrint), text)
#ifndef NOTESTS
import Formulas (overatoms, onatoms)
#endif

-- | Literals are the building blocks of the clause and implicative normal
-- forms.  They support negation and must include True and False elements.
class (IsFormula lit atom,
       IsNegatable lit,
       HasBoolean lit)
    => IsLiteral lit atom where
    -- | This is the internal fold for literals, 'foldLiteral' below should
    -- normally be used, but its argument must be an instance of 'JustLiteral'.
    foldLiteral' :: (lit -> r) -- ^ Called for higher order formulas (non-literal)
                 -> (lit -> r) -- ^ Called for negated formulas
                 -> (Bool -> r) -- ^ Called for true and false formulas
                 -> (atom -> r) -- ^ Called for atomic formulas
                 -> lit -> r

foldLiteral :: IsLiteral lit atom => (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r
foldLiteral = foldLiteral' (error "JustLiteral failure")

-- | Class that indicates that a formula type *only* contains 'IsLiteral'
-- features - no combinations or quantifiers.
class JustLiteral formula

-- | Combine two literals (internal version).
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

-- | Combine two literals.
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

fixityLiteral :: (IsLiteral lit atom, JustLiteral lit) => lit -> Fixity
fixityLiteral fm =
    foldLiteral ne tf at fm
    where
      ne _ = Fixity 5 InfixA
      tf _ = Fixity 10 InfixN
      at = fixity

-- | Implementation of 'pPrint' for -- 'JustLiteral' types.
prettyLiteral :: (IsLiteral lit atom, JustLiteral lit) => lit -> Doc
prettyLiteral lit =
    foldLiteral ne tf at lit
    where
      ne p = text "¬" <> prettyLiteral p
      tf = pPrint
      at a = pPrint a

showLiteral :: (IsLiteral lit atom, JustLiteral lit) => lit -> String
showLiteral lit = foldLiteral ne tf at lit
    where
      ne p = "(.~.)(" ++ showLiteral p ++ ")"
      tf = show
      at = show

-- | Implementation of 'onatoms' for 'JustLiteral' types.
onatomsLiteral :: IsLiteral lit atom => (atom -> lit) -> lit -> lit
onatomsLiteral f fm =
    foldLiteral ne tf at fm
    where
      ne p = onatomsLiteral f p
      tf flag = fromBool flag
      at x = f x

-- | implementation of 'overatoms' for 'JustLiteral' types.
overatomsLiteral :: (IsLiteral lit atom, JustLiteral lit) => (atom -> r -> r) -> lit -> r -> r
overatomsLiteral f fm r0 =
        foldLiteral ne (const r0) (flip f r0) fm
        where
          ne fm' = overatomsLiteral f fm' r0

#ifndef NOTESTS
-- | Example of a 'JustLiteral' type.
data LFormula atom
    = F
    | T
    | Atom atom
    | Not (LFormula atom)
    deriving (Eq, Ord, Read, Show)

instance JustLiteral (LFormula atom)

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

instance (Ord atom, Pretty atom, HasFixity atom, Show atom) => IsFormula (LFormula atom) atom where
    atomic = Atom
    overatoms = overatomsLiteral
    onatoms = onatomsLiteral

instance IsFormula (LFormula atom) atom => IsLiteral (LFormula atom) atom where
    foldLiteral' _ ne tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not f -> ne f

instance (Ord atom, Pretty atom, HasFixity atom, Show atom) => HasFixity (LFormula atom) where
    fixity = fixityLiteral

instance IsLiteral (LFormula atom) atom => Pretty (LFormula atom) where
    pPrint = prettyLiteral
#endif
