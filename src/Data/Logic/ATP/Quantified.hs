-- | 'IsQuantified' is a subclass of 'IsPropositional' of formula
-- types that support existential and universal quantification.

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

module Data.Logic.ATP.Quantified
    ( Quant((:!:), (:?:))
    , IsQuantified(VarOf, quant, foldQuantified)
    , for_all, (∀)
    , exists, (∃)
    , precedenceQuantified
    , associativityQuantified
    , prettyQuantified
    , showQuantified
    , zipQuantified
    , convertQuantified
    , onatomsQuantified
    , overatomsQuantified
    -- * Concrete instance of a quantified formula type
    , QFormula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    ) where

import Data.Data (Data)
import Data.Logic.ATP.Apply (HasApply(TermOf))
import Data.Logic.ATP.Formulas (fromBool, IsAtom, IsFormula(..), onatoms, prettyBool)
import Data.Logic.ATP.Lit ((.~.), IsLiteral(foldLiteral'), IsLiteral(..))
import Data.Logic.ATP.Pretty as Pretty
    ((<>), Associativity(InfixN, InfixR, InfixA), Doc, HasFixity(precedence, associativity),
     Precedence, Side(Top, LHS, RHS, Unary), testParen, text,
     andPrec, orPrec, impPrec, iffPrec, notPrec, leafPrec, quantPrec)
import Data.Logic.ATP.Prop (BinOp(..), binop, IsPropositional((.&.), (.|.), (.=>.), (.<=>.), foldPropositional', foldCombination))
import Data.Logic.ATP.Term (IsTerm(TVarOf), IsVariable)
import Data.Typeable (Typeable)
import Prelude hiding (pred)
import Text.PrettyPrint (fsep)
import Text.PrettyPrint.HughesPJClass (maybeParens, Pretty(pPrint, pPrintPrec), PrettyLevel, prettyNormal)

-------------------------
-- QUANTIFIED FORMULAS --
-------------------------

-- | The two types of quantification
data Quant
    = (:!:) -- ^ for_all
    | (:?:) -- ^ exists
    deriving (Eq, Ord, Data, Typeable, Show)

-- | Class of quantified formulas.
class (IsPropositional formula, IsVariable (VarOf formula)) => IsQuantified formula where
    type (VarOf formula) -- A type function mapping formula to the associated variable
    quant :: Quant -> VarOf formula -> formula -> formula
    foldQuantified :: (Quant -> VarOf formula -> formula -> r)
                   -> (formula -> BinOp -> formula-> r)
                   -> (formula -> r)
                   -> (Bool -> r)
                   -> (AtomOf formula -> r)
                   -> formula -> r

for_all :: IsQuantified formula => VarOf formula -> formula -> formula
for_all = quant (:!:)
exists :: IsQuantified formula => VarOf formula -> formula -> formula
exists = quant (:?:)

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: IsQuantified formula => VarOf formula -> formula -> formula
infixr 1 ∀
(∀) = for_all
(∃) :: IsQuantified formula => VarOf formula -> formula -> formula
infixr 1 ∃
(∃) = exists

precedenceQuantified :: forall formula. IsQuantified formula => formula -> Precedence
precedenceQuantified = foldQuantified qu co ne tf at
    where
      qu _ _ _ = quantPrec
      co _ (:&:) _ = andPrec
      co _ (:|:) _ = orPrec
      co _ (:=>:) _ = impPrec
      co _ (:<=>:) _ = iffPrec
      ne _ = notPrec
      tf _ = leafPrec
      at = precedence

associativityQuantified :: forall formula. IsQuantified formula => formula -> Associativity
associativityQuantified = foldQuantified qu co ne tf at
    where
      qu _ _ _ = Pretty.InfixR
      ne _ = Pretty.InfixA
      co _ (:&:) _ = Pretty.InfixA
      co _ (:|:) _ = Pretty.InfixA
      co _ (:=>:) _ = Pretty.InfixR
      co _ (:<=>:) _ = Pretty.InfixA
      tf _ = Pretty.InfixN
      at = associativity

-- | Implementation of 'Pretty' for 'IsQuantified' types.
prettyQuantified :: forall fof v. (IsQuantified fof, v ~ VarOf fof) =>
                    Side -> PrettyLevel -> Rational -> fof -> Doc
prettyQuantified side l r fm =
    maybeParens (l > prettyNormal || testParen side r (precedence fm) (associativity fm)) $ foldQuantified (\op v p -> qu op [v] p) co ne tf at fm
    -- maybeParens (r > precedence fm) $ foldQuantified (\op v p -> qu op [v] p) co ne tf at fm
    where
      -- Collect similarly quantified variables
      qu :: Quant -> [v] -> fof -> Doc
      qu op vs p' = foldQuantified (qu' op vs p') (\_ _ _ -> qu'' op vs p') (\_ -> qu'' op vs p')
                                                      (\_ -> qu'' op vs p') (\_ -> qu'' op vs p') p'
      qu' :: Quant -> [v] -> fof -> Quant -> v -> fof -> Doc
      qu' op vs _ op' v p' | op == op' = qu op (v : vs) p'
      qu' op vs p _ _ _ = qu'' op vs p
      qu'' :: Quant -> [v] -> fof -> Doc
      qu'' _op [] p = prettyQuantified Unary l r p
      qu'' op vs p = text (case op of (:!:) -> "∀"; (:?:) -> "∃") <>
                     fsep (map pPrint (reverse vs)) <>
                     text ". " <> prettyQuantified Unary l (precedence fm + 1) p
      co :: fof -> BinOp -> fof -> Doc
      co p (:&:) q = prettyQuantified LHS l (precedence fm) p <> text "∧" <>  prettyQuantified RHS l (precedence fm) q
      co p (:|:) q = prettyQuantified LHS l (precedence fm) p <> text "∨" <> prettyQuantified RHS l (precedence fm) q
      co p (:=>:) q = prettyQuantified LHS l (precedence fm) p <> text "⇒" <> prettyQuantified RHS l (precedence fm) q
      co p (:<=>:) q = prettyQuantified LHS l (precedence fm) p <> text "⇔" <> prettyQuantified RHS l (precedence fm) q
      ne p = text "¬" <> prettyQuantified Unary l (precedence fm) p
      tf x = prettyBool x
      at x = pPrintPrec l r x -- maybeParens (d > PrettyLevel atomPrec) $ pPrint x

-- | Implementation of 'showsPrec' for 'IsQuantified' types.
showQuantified :: IsQuantified formula => Side -> Int -> formula -> ShowS
showQuantified side r fm =
    showParen (testParen side r (precedence fm) (associativity fm)) $ foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = showString "for_all " . showString (show x) . showString " " . showQuantified Unary (precedence fm + 1) p
      qu (:?:) x p = showString "exists " . showString (show x) . showString " " . showQuantified Unary (precedence fm + 1) p
      co p (:&:) q = showQuantified LHS (precedence fm) p . showString " .&. " . showQuantified RHS (precedence fm) q
      co p (:|:) q = showQuantified LHS (precedence fm) p . showString " .|. " . showQuantified RHS (precedence fm) q
      co p (:=>:) q = showQuantified LHS (precedence fm) p . showString " .=>. " . showQuantified RHS (precedence fm) q
      co p (:<=>:) q = showQuantified LHS (precedence fm) p . showString " .<=>. " . showQuantified RHS (precedence fm) q
      ne p = showString "(.~.) " . showQuantified Unary (succ (precedence fm)) p
      tf x = showsPrec (precedence fm) x
      at x = showsPrec (precedence fm) x

-- | Combine two formulas if they are similar.
zipQuantified :: IsQuantified formula =>
                 (Quant -> VarOf formula -> formula -> Quant -> VarOf formula -> formula -> Maybe r)
              -> (formula -> BinOp -> formula -> formula -> BinOp -> formula -> Maybe r)
              -> (formula -> formula -> Maybe r)
              -> (Bool -> Bool -> Maybe r)
              -> ((AtomOf formula) -> (AtomOf formula) -> Maybe r)
              -> formula -> formula -> Maybe r
zipQuantified qu co ne tf at fm1 fm2 =
    foldQuantified qu' co' ne' tf' at' fm1
    where
      qu' op1 v1 p1 = foldQuantified (qu op1 v1 p1)       (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      co' l1 op1 r1 = foldQuantified (\ _ _ _ -> Nothing) (co l1 op1 r1)       (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      ne' x1 =        foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (ne x1)          (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 =        foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ -> Nothing) (tf x1)          (\ _ -> Nothing) fm2
      at' atom1 =     foldQuantified (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at atom1)       fm2

-- | Convert any instance of IsQuantified to any other by
-- specifying the result type.
convertQuantified :: forall f1 f2.
                     (IsQuantified f1, IsQuantified f2) =>
                     (AtomOf f1 -> AtomOf f2) -> (VarOf f1 -> VarOf f2) -> f1 -> f2
convertQuantified ca cv f1 =
    foldQuantified qu co ne tf at f1
    where
      qu :: Quant -> VarOf f1 -> f1 -> f2
      qu (:!:) x p = for_all (cv x :: VarOf f2) (convertQuantified ca cv p :: f2)
      qu (:?:) x p = exists (cv x :: VarOf f2) (convertQuantified ca cv p :: f2)
      co p (:&:) q = convertQuantified ca cv p .&. convertQuantified ca cv q
      co p (:|:) q = convertQuantified ca cv p .|. convertQuantified ca cv q
      co p (:=>:) q = convertQuantified ca cv p .=>. convertQuantified ca cv q
      co p (:<=>:) q = convertQuantified ca cv p .<=>. convertQuantified ca cv q
      ne p = (.~.) (convertQuantified ca cv p)
      tf :: Bool -> f2
      tf = fromBool
      at :: AtomOf f1 -> f2
      at = atomic . ca

onatomsQuantified :: IsQuantified formula => (AtomOf formula -> AtomOf formula) -> formula -> formula
onatomsQuantified f fm =
    foldQuantified qu co ne tf at fm
    where
      qu op v p = quant op v (onatomsQuantified f p)
      ne p = (.~.) (onatomsQuantified f p)
      co p op q = binop (onatomsQuantified f p) op (onatomsQuantified f q)
      tf flag = fromBool flag
      at x = atomic (f x)

overatomsQuantified :: IsQuantified fof => (AtomOf fof -> r -> r) -> fof -> r -> r
overatomsQuantified f fof r0 =
    foldQuantified qu co ne (const r0) (flip f r0) fof
    where
      qu _ _ fof' = overatomsQuantified f fof' r0
      ne fof' = overatomsQuantified f fof' r0
      co p _ q = overatomsQuantified f p (overatomsQuantified f q r0)

data QFormula v atom
    = F
    | T
    | Atom atom
    | Not (QFormula v atom)
    | And (QFormula v atom) (QFormula v atom)
    | Or (QFormula v atom) (QFormula v atom)
    | Imp (QFormula v atom) (QFormula v atom)
    | Iff (QFormula v atom) (QFormula v atom)
    | Forall v (QFormula v atom)
    | Exists v (QFormula v atom)
    deriving (Eq, Ord, Data, Typeable, Read)

instance (HasApply atom, IsTerm term, term ~ TermOf atom, v ~ TVarOf term) => Pretty (QFormula v atom) where
    pPrintPrec = prettyQuantified Top

-- The IsFormula instance for QFormula
instance (HasApply atom, v ~ TVarOf (TermOf atom)) => IsFormula (QFormula v atom) where
    type AtomOf (QFormula v atom) = atom
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    true = T
    false = F
    atomic = Atom
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified

instance (IsFormula (QFormula v atom), HasApply atom, v ~ TVarOf (TermOf atom)) => IsPropositional (QFormula v atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff
    foldPropositional' ho co ne tf at fm =
        case fm of
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          _ -> foldLiteral' ho ne tf at fm
    foldCombination other dj cj imp iff fm =
        case fm of
          Or a b -> a `dj` b
          And a b -> a `cj` b
          Imp a b -> a `imp` b
          Iff a b -> a `iff` b
          _ -> other fm

instance (IsPropositional (QFormula v atom), IsVariable v, IsAtom atom) => IsQuantified (QFormula v atom) where
    type VarOf (QFormula v atom) = v
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldQuantified qu _co _ne _tf _at (Forall v fm) = qu (:!:) v fm
    foldQuantified qu _co _ne _tf _at (Exists v fm) = qu (:?:) v fm
    foldQuantified _qu co ne tf at fm =
        foldPropositional' (\_ -> error "IsQuantified QFormula") co ne tf at fm

-- Build a Haskell expression for this formula
instance IsQuantified (QFormula v atom) => Show (QFormula v atom) where
    showsPrec = showQuantified Top

-- Precedence information for QFormula
instance IsQuantified (QFormula v atom) => HasFixity (QFormula v atom) where
    precedence = precedenceQuantified
    associativity = associativityQuantified

instance (HasApply atom, v ~ TVarOf (TermOf atom)) => IsLiteral (QFormula v atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x
    foldLiteral' ho ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> ne p
          _ -> ho fm
