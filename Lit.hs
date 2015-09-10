{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lit
    ( IsLiteral(foldLiteral)
    , zipLiterals
    , prettyLit
    -- , foldAtomsLiteral
    , LFormula(T, F, Atom, Not)
    ) where

import Data.Monoid ((<>))
import Formulas (HasBoolean(..), IsNegatable(..), IsFormula)
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixN))
import Pretty (Doc, HasFixity(fixity), nest, parens, Pretty(pPrint), text)
import Prelude hiding (negate, null)

-- | Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (IsFormula lit atom, IsNegatable lit, HasBoolean lit) => IsLiteral lit atom | lit -> atom where
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

prettyLit :: forall lit atom v. (IsLiteral lit atom, HasFixity atom) =>
              (Fixity -> atom -> Doc)
           -> (v -> Doc)
           -> Fixity
           -> lit
           -> Doc
prettyLit pa pv pprec lit =
    parensIf (pprec > prec) $ foldLiteral neg tf at lit
    where
      neg :: lit -> Doc
      neg x = text "¬" <> prettyLit pa pv (Fixity 6 InfixN) x
      tf = pPrint
      at x = pa (Fixity 6 InfixN) x
      parensIf False = id
      parensIf _ = parens . nest 1
      prec = fixityLiteral lit

fixityLiteral :: (IsLiteral formula atom, HasFixity atom) => formula -> Fixity
fixityLiteral formula =
    foldLiteral neg tf at formula
    where
      neg _ = Fixity 5 InfixN
      tf _ = Fixity 10 InfixN
      at = fixity

-- foldAtomsLiteral :: IsLiteral lit atom => (r -> atom -> r) -> r -> lit -> r
-- foldAtomsLiteral f i lit = overatoms (flip f) lit i

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

instance IsNegatable (LFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x
