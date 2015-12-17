-- | ATOM with a distinguished Equate predicate.

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.Equate
    ( HasEquate(equate, foldEquate)
    , (.=.)
    , zipEquates
    , prettyEquate
    , overtermsEq
    , ontermsEq
    , showApplyAndEquate
    , showEquate
    , convertEquate
    , precedenceEquate
    , associativityEquate
    , FOL(R, Equals)
    , EqAtom
    ) where

import Data.Data (Data)
import Data.Logic.ATP.Apply (HasApply(PredOf, TermOf, applyPredicate, foldApply', overterms, onterms),
                             IsPredicate, Predicate, prettyApply, showApply)
import Data.Logic.ATP.Formulas (IsAtom, IsFormula(..))
import Data.Logic.ATP.Pretty as Pretty ((<>), Associativity(InfixN), atomPrec, Doc, eqPrec, HasFixity(associativity, precedence), pAppPrec, Precedence, text)
import Data.Logic.ATP.Term (FTerm, IsTerm)
import Data.Typeable (Typeable)
import Prelude hiding (pred)
import Text.PrettyPrint.HughesPJClass (maybeParens, Pretty(pPrintPrec), PrettyLevel)

-- | Atoms that support equality must be an instance of HasEquate
class HasApply atom => HasEquate atom where
    equate :: TermOf atom -> TermOf atom -> atom
    -- ^ Create an equate predicate
    foldEquate :: (TermOf atom -> TermOf atom -> r) -> (PredOf atom -> [TermOf atom] -> r) -> atom -> r
    -- ^ Analyze whether a predicate is an equate or a regular apply.

-- | Combine 'equate' and 'atomic' to build a formula from two terms.
(.=.) :: (IsFormula formula, HasEquate atom, atom ~ AtomOf formula) => TermOf atom -> TermOf atom -> formula
a .=. b = atomic (equate a b)
infix 6 .=.

-- | Zip two atoms that support equality
zipEquates :: (HasEquate atom1, HasEquate atom2, PredOf atom1 ~ PredOf atom2) =>
              (TermOf atom1 -> TermOf atom1 ->
               TermOf atom2 -> TermOf atom2 -> Maybe r)
           -> (PredOf atom1 -> [(TermOf atom1, TermOf atom2)] -> Maybe r)
           -> atom1 -> atom2 -> Maybe r
zipEquates eq ap atom1 atom2 =
    foldEquate eq' ap' atom1
    where
      eq' l1 r1 = foldEquate (eq l1 r1) (\_ _ -> Nothing) atom2
      ap' p1 ts1 = foldEquate (\_ _ -> Nothing) (ap'' p1 ts1) atom2
      ap'' p1 ts1 p2 ts2 | p1 == p2 && length ts1 == length ts2 = ap p1 (zip ts1 ts2)
      ap'' _ _ _ _ = Nothing

-- | Convert between HasEquate atom types.
convertEquate :: (HasEquate atom1, HasEquate atom2) =>
                 (PredOf atom1 -> PredOf atom2) -> (TermOf atom1 -> TermOf atom2) -> atom1 -> atom2
convertEquate cp ct = foldEquate (\t1 t2 -> equate (ct t1) (ct t2)) (\p1 ts1 -> applyPredicate (cp p1) (map ct ts1))

-- | Implementation of 'overterms' for 'HasEquate' types.
overtermsEq :: HasEquate atom => ((TermOf atom) -> r -> r) -> r -> atom -> r
overtermsEq f r0 = foldEquate (\t1 t2 -> f t2 (f t1 r0)) (\_ ts -> foldr f r0 ts)

-- | Implementation of 'onterms' for 'HasEquate' types.
ontermsEq :: HasEquate atom => ((TermOf atom) -> (TermOf atom)) -> atom -> atom
ontermsEq f = foldEquate (\t1 t2 -> equate (f t1) (f t2)) (\p ts -> applyPredicate p (map f ts))

-- | Implementation of Show for 'HasEquate' types
showApplyAndEquate :: (HasEquate atom, Show (TermOf atom)) => atom -> String
showApplyAndEquate atom = foldEquate showEquate showApply atom

showEquate :: Show term => term -> term -> String
showEquate t1 t2 = "(" ++ show t1 ++ ") .=. (" ++ show t2 ++ ")"

-- | Format the infix equality predicate applied to two terms.
prettyEquate :: IsTerm term => PrettyLevel -> Rational -> term -> term -> Doc
prettyEquate l p t1 t2 =
    maybeParens (p > atomPrec) $ pPrintPrec l atomPrec t1 <> text "=" <> pPrintPrec l atomPrec t2

precedenceEquate :: HasEquate atom => atom -> Precedence
precedenceEquate = foldEquate (\_ _ -> eqPrec) (\_ _ -> pAppPrec)

associativityEquate :: HasEquate atom => atom -> Associativity
associativityEquate = foldEquate (\_ _ -> Pretty.InfixN) (\_ _ -> Pretty.InfixN)

-- | Instance of an atom type with a distinct equality predicate.
data FOL predicate term = R predicate [term] | Equals term term deriving (Eq, Ord, Data, Typeable, Read)

instance (IsPredicate predicate, IsTerm term) => HasEquate (FOL predicate term) where
    equate lhs rhs = Equals lhs rhs
    foldEquate eq _ (Equals lhs rhs) = eq lhs rhs
    foldEquate _ ap (R p ts) = ap p ts

instance (IsPredicate predicate, IsTerm term) => IsAtom (FOL predicate term)

instance (HasApply (FOL predicate term),
          HasEquate (FOL predicate term), IsTerm term) => Pretty (FOL predicate term) where
    pPrintPrec d r = foldEquate (prettyEquate d r) prettyApply

instance (IsPredicate predicate, IsTerm term) => HasApply (FOL predicate term) where
    type PredOf (FOL predicate term) = predicate
    type TermOf (FOL predicate term) = term
    applyPredicate = R
    foldApply' _ f (R p ts) = f p ts
    foldApply' d _ x = d x
    overterms = overtermsEq
    onterms = ontermsEq

instance (IsPredicate predicate, IsTerm term, Show predicate, Show term) => Show (FOL predicate term) where
    show = foldEquate (\t1 t2 -> showEquate (t1 :: term) (t2 :: term))
                      (\p ts -> showApply (p :: predicate) (ts :: [term]))

instance  (IsPredicate predicate, IsTerm term) => HasFixity (FOL predicate term) where
    precedence = precedenceEquate
    associativity = associativityEquate

-- | An atom type with equality predicate
type EqAtom = FOL Predicate FTerm
