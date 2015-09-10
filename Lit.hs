{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lit
    ( IsLiteral(foldLiteral)
    , zipLiterals
    , prettyLit
    , foldAtomsLiteral
    ) where

import Data.Bool (bool)
import Data.Foldable as Foldable (null)
import Data.List as List (map)
import Data.Map as Map (Map)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, fromList, intersection, isProperSubsetOf, map, minView, partition, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import Formulas (atom_union,
                 HasBoolean(fromBool, asBool), true, false, prettyBool,
                 IsNegatable, (.~.), negate, positive,
                 IsCombinable((.&.), (.|.), (.=>.), (.<=>.)), (¬), (∧), (∨),
                 Combination((:~:), BinOp), BinOp((:&:), (:|:), (:=>:), (:<=>:)),
                 IsFormula(atomic), onatoms,
                 PFormula(T, F, Atom, Not, And, Or, Imp, Iff))
import Language.Haskell.TH.Syntax as TH (Fixity(Fixity), FixityDirection(InfixN))
import Lib (fpf, (|=>), allpairs, setAny)
import Pretty (botFixity, Doc, HasFixity(fixity), nest, parens, Pretty(pPrint), prettyShow, text, topFixity)
import Prelude hiding (negate, null)
import Test.HUnit (Test(TestCase, TestLabel, TestList), assertEqual)

-- | Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (IsFormula lit atom, IsNegatable lit, HasBoolean lit,
       Pretty lit -- for debugging
      {-, HasFixity atom, Ord lit-}) => IsLiteral lit atom | lit -> atom where
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
      tf x = prettyBool x
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

foldAtomsLiteral :: IsLiteral lit atom => (r -> atom -> r) -> r -> lit -> r
foldAtomsLiteral f i lit = foldLiteral (foldAtomsLiteral f i) (const i) (f i) lit
