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
{-# LANGUAGE TypeSynonymInstances #-}

module Data.Logic.ATP.Apply
    ( IsPredicate
    , HasApply(TermOf, PredOf, applyPredicate, foldApply', overterms, onterms)
    , atomFuncs
    , functions
    , JustApply
    , foldApply
    , prettyApply
    , overtermsApply
    , ontermsApply
    , zipApplys
    , showApply
    , convertApply
    , onformula
    , pApp
    , FOLAP(AP)
    , Predicate
    , ApAtom
    ) where

import Data.Data (Data)
import Data.Logic.ATP.Formulas (IsAtom, IsFormula(..), onatoms)
import Data.Logic.ATP.Pretty as Pretty ((<>), Associativity(InfixN), Doc, HasFixity(associativity, precedence), pAppPrec, text)
import Data.Logic.ATP.Term (Arity, FTerm, IsTerm(FunOf, TVarOf), funcs)
import Data.Set as Set (Set, union)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Prelude hiding (pred)
import Text.PrettyPrint (parens, brackets, punctuate, comma, fcat, space)
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint))

---------------------------
-- ATOMS (Atomic Formula) AND PREDICATES --
---------------------------

-- | A predicate is the thing we apply to a list of 'IsTerm's to make
-- an 'IsAtom'.
class (Eq predicate, Ord predicate, Show predicate, IsString predicate, Pretty predicate) => IsPredicate predicate

-- | The result of applying a predicate to some terms is an atomic
-- formula whose type is an instance of 'HasApply'.
class (IsAtom atom, IsPredicate (PredOf atom), IsTerm (TermOf atom)) => HasApply atom where
    type PredOf atom
    type TermOf atom
    applyPredicate :: PredOf atom -> [(TermOf atom)] -> atom
    foldApply' :: (atom -> r) -> (PredOf atom -> [TermOf atom] -> r) -> atom -> r
    overterms :: (TermOf atom -> r -> r) -> r -> atom -> r
    onterms :: (TermOf atom -> TermOf atom) -> atom -> atom

-- | The set of functions in an atom.
atomFuncs :: (HasApply atom, function ~ FunOf (TermOf atom)) => atom -> Set (function, Arity)
atomFuncs = overterms (Set.union . funcs) mempty

-- | The set of functions in a formula.
functions :: (IsFormula formula, HasApply atom, Ord function,
              atom ~ AtomOf formula,
              term ~ TermOf atom,
              function ~ FunOf term) =>
             formula -> Set (function, Arity)
functions fm = overatoms (Set.union . atomFuncs) fm mempty

-- | Atoms that have apply but do not support equate
class HasApply atom => JustApply atom

foldApply :: (JustApply atom, term ~ TermOf atom) => (PredOf atom -> [term] -> r) -> atom -> r
foldApply = foldApply' (error "JustApply failure")

-- | Pretty print prefix application of a predicate
prettyApply :: (v ~ TVarOf term, IsPredicate predicate, IsTerm term) => predicate -> [term] -> Doc
prettyApply p ts = pPrint p <> parens (fcat (punctuate comma (map pPrint ts)))

-- | Implementation of 'overterms' for 'HasApply' types.
overtermsApply :: JustApply atom => ((TermOf atom) -> r -> r) -> r -> atom -> r
overtermsApply f r0 = foldApply (\_ ts -> foldr f r0 ts)

-- | Implementation of 'onterms' for 'HasApply' types.
ontermsApply :: JustApply atom => ((TermOf atom) -> (TermOf atom)) -> atom -> atom
ontermsApply f = foldApply (\p ts -> applyPredicate p (map f ts))

-- | Zip two atoms if they are similar
zipApplys :: (JustApply atom1, term ~ TermOf atom1, predicate ~ PredOf atom1,
              JustApply atom2, term ~ TermOf atom2, predicate ~ PredOf atom2) =>
             (predicate -> [(term, term)] -> Maybe r) -> atom1 -> atom2 -> Maybe r
zipApplys f atom1 atom2 =
    foldApply f' atom1
    where
      f' p1 ts1 = foldApply (\p2 ts2 ->
                                     if p1 /= p2 || length ts1 /= length ts2
                                     then Nothing
                                     else f p1 (zip ts1 ts2)) atom2

-- | Implementation of 'Show' for 'JustApply' types
showApply :: (Show predicate, Show term) => predicate -> [term] -> String
showApply p ts = show (text "pApp " <> parens (text (show p)) <> brackets (fcat (punctuate (comma <> space) (map (text . show) ts))))

-- | Convert between two instances of 'HasApply'
convertApply :: (JustApply atom1, HasApply atom2) =>
                (PredOf atom1 -> PredOf atom2) -> (TermOf atom1 -> TermOf atom2) -> atom1 -> atom2
convertApply cp ct = foldApply (\p1 ts1 -> applyPredicate (cp p1) (map ct ts1))

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (IsFormula formula, HasApply atom, atom ~ AtomOf formula, term ~ TermOf atom) =>
             (term -> term) -> formula -> formula
onformula f = onatoms (onterms f)

-- | Build a formula from a predicate and a list of terms.
pApp :: (IsFormula formula, HasApply atom, atom ~ AtomOf formula) => PredOf atom -> [TermOf atom] -> formula
pApp p args = atomic (applyPredicate p args)

-- | First order logic formula atom type.
data FOLAP predicate term = AP predicate [term] deriving (Eq, Ord, Data, Typeable, Read)

instance (IsPredicate predicate, IsTerm term) => JustApply (FOLAP predicate term)

instance (IsPredicate predicate, IsTerm term) => IsAtom (FOLAP predicate term)

instance (IsPredicate predicate, IsTerm term) => Pretty (FOLAP predicate term) where
    pPrint = foldApply prettyApply

instance (IsPredicate predicate, IsTerm term) => HasApply (FOLAP predicate term) where
    type PredOf (FOLAP predicate term) = predicate
    type TermOf (FOLAP predicate term) = term
    applyPredicate = AP
    foldApply' _ f (AP p ts) = f p ts
    overterms f r (AP _ ts) = foldr f r ts
    onterms f (AP p ts) = AP p (map f ts)

instance (IsPredicate predicate, IsTerm term, Show predicate, Show term) => Show (FOLAP predicate term) where
    show = foldApply (\p ts -> showApply (p :: predicate) (ts :: [term]))

instance HasFixity (FOLAP predicate term) where
    precedence _ = pAppPrec
    associativity _ = Pretty.InfixN

-- | A predicate type with no distinct equality.
data Predicate = NamedPred String
    deriving (Eq, Ord, Data, Typeable, Read)

instance IsString Predicate where

    -- fromString "True" = error "bad predicate name: True"
    -- fromString "False" = error "bad predicate name: True"
    -- fromString "=" = error "bad predicate name: True"
    fromString s = NamedPred s

instance Show Predicate where
    show (NamedPred s) = "fromString " ++ show s

instance Pretty Predicate where
    pPrint (NamedPred "=") = error "Use of = as a predicate name is prohibited"
    pPrint (NamedPred "True") = error "Use of True as a predicate name is prohibited"
    pPrint (NamedPred "False") = error "Use of False as a predicate name is prohibited"
    pPrint (NamedPred s) = text s

instance IsPredicate Predicate

-- | An atom type with no equality predicate
type ApAtom = FOLAP Predicate FTerm
instance JustApply ApAtom
