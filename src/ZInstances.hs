{-# LANGUAGE FlexibleInstances, TypeFamilies #-}
module ZInstances where

import Data.Set as Set
import Data.String (IsString(fromString))
import Formulas
import Pretty
import Lit hiding (LFormula(..))
import Prop hiding (PFormula(..))
import FOL hiding (Formula(..), FOL(..), FOLEQ(..), Term(..), FName)
import ZTypes

instance Pretty (Formula FOL) where
    pPrint = prettyQuantified

instance HasBoolean (Formula FOL) where
    asBool TT = Just True
    asBool FF = Just False
    asBool _ = Nothing
    fromBool True = TT
    fromBool False = FF

instance IsNegatable (Formula FOL) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance IsCombinable (Formula FOL) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff
    foldCombination other dj cj imp iff fm =
        case fm of
          Or a b -> a `dj` b
          And a b -> a `cj` b
          Imp a b -> a `imp` b
          Iff a b -> a `iff` b
          _ -> other fm

-- The IsFormula instance for Formula
instance IsFormula (Formula FOL) where
    type AtomOf (Formula FOL) = FOL
    atomic = Atom
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified

instance IsPropositional (Formula FOL) where
    foldPropositional' ho co ne tf at fm =
        case fm of
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          _ -> foldLiteral' ho ne tf at fm

instance IsQuantified (Formula FOL) where
    type VarOf (Formula FOL) = V
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldQuantified qu _co _ne _tf _at (Forall v fm) = qu (:!:) v fm
    foldQuantified qu _co _ne _tf _at (Exists v fm) = qu (:?:) v fm
    foldQuantified _qu co ne tf at fm =
        foldPropositional' (\_ -> error "IsQuantified Formula") co ne tf at fm

-- Build a Haskell expression for this formula
{-
instance Show (Formula FOL) where
    show = showQuantified
-}

-- Precedence information for Formula
instance HasFixity (Formula FOL) where
    fixity = fixityQuantified

instance IsLiteral (Formula FOL) where
    foldLiteral' ho ne tf at fm =
        case fm of
          TT -> tf True
          FF -> tf False
          Atom a -> at a
          Not p -> ne p
          _ -> ho fm

instance JustApply FOL

instance IsAtom FOL

instance Pretty FOL where
    pPrint = foldApply prettyApply -- foldEquate prettyEquate prettyApply

instance IsPredicate String

instance IsString Term where
    fromString = Var . fromString

{-
instance Show Term where
    show = showTerm
-}

instance Pretty Term where
    pPrint = prettyTerm

instance IsString Function where
    fromString = FName


instance Pretty Function where
    pPrint (FName s) = text s

instance IsFunction Function where
    variantFunction f@(FName s) fns | Set.member f fns = variantFunction (FName (s ++ "'")) fns
    variantFunction f@(Skolem s) fns | Set.member f fns = variantFunction (Skolem (s ++ "'")) fns
    variantFunction f _ = f

instance IsTerm Term where
    type TVarOf Term = V
    type FunOf Term = Function
    vt = Var
    fApp = Fn
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          Fn f ts -> fn f ts

instance HasApply FOL where
    type PredOf FOL = String
    type TermOf FOL = Term
    applyPredicate = R
    foldApply' _ f (R p ts) = f p ts
    foldApply' d _ x = d x
    overterms = overtermsApply -- overtermsEq
    onterms = ontermsApply -- ontermsEq

{-
instance Show FOL where
    show = foldEquate (\t1 t2 -> showEquate (t1 :: term) (t2 :: term))
                      (\p ts -> showApply (p :: predicate) (ts :: [term]))
-}
{-
instance HasApplyAndEquate FOL where
    equate lhs rhs = Equals lhs rhs
    foldEquate eq _ (Equals lhs rhs) = eq lhs rhs
    foldEquate _ ap (AP p ts) = ap p ts
-}

instance HasFixity FOL where
    fixity _ = Fixity 6 InfixN

instance IsFirstOrder (Formula FOL)
