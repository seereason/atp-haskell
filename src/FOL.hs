-- | Basic stuff for first order logic.  'IsQuantified' is a subclass
-- of 'IsPropositional' of formula types that support existential and
-- universal quantification.
--
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module FOL
    ( -- * Variables
      IsVariable(variant, prefix), variants --, showVariable
    -- * Functions
    , IsFunction
    , Arity
    , HasFunctions(funcs)
    -- * Terms
    , IsTerm(vt, fApp, foldTerm), zipTerms, termFuncs, convertTerm, prettyTerm, showTerm
    -- * Predicates
    , IsPredicate{-(prettyPredicateApplication, prettyPredicateEquate)-}, prettyApply, prettyEquate
    -- * Atoms
    , HasApply(TermOf, PredOf, applyPredicate, foldPredicate', overterms, onterms), foldPredicate, JustApply
    , overtermsApply, ontermsApply, showApply
    -- * Atoms supporting Equate
    , HasApplyAndEquate(equate, foldEquate)
    , overtermsEq, ontermsEq
    , convertPredicate, convertPredicateEq
    , zipPredicates, zipPredicatesEq
    , pApp, atomFuncs
    , isEquate, (.=.), showEquate, showApplyAndEquate
    -- * Quantified Formulas
    , Quant((:!:), (:?:))
    , IsQuantified(VarOf, quant, foldQuantified), for_all, exists, (∀), (∃)
    , quantifiedFuncs
    , propositionalFuncs
    , showQuantified
    , prettyQuantified
    , IsFirstOrder
    , zipQuantified
    , fixityQuantified
    , convertQuantified
    , onatomsQuantified
    , overatomsQuantified
    , onformula
    -- * Semantics
    , Interp
    , termval
    , holds
    , bool_interp
    , mod_interp
    -- * Free Variables
    , var
    , fv, fvp, fvl, fva, fvt
    , generalize
    -- * Substitution
    , subst, substq, asubst, tsubst, lsubst
#ifndef NOTESTS
    -- * Instances
    , V(V)
    , FName(FName)
    , Term(Var, FApply)
    , Predicate
    , FOL(R)
    , FOLEQ(AP, Equals)
    , Formula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    , MyTerm1, MyAtom1, MyAtom2, MyFormula1
    -- * Tests
    , testFOL
#endif
    ) where

import Data.Data (Data)
--import Data.Function (on)
import Data.Map as Map (insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Set as Set (difference, empty, fold, insert, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Formulas ((.~.), BinOp(..), binop, false, HasBoolean(..), IsCombinable(..), IsFormula(..),
                 onatoms, prettyBool, true)
import Lib (Marked(Mark, unMark'), setAny, tryApplyD, undefine, (|->))
import Lit (foldLiteral, IsLiteral)
import Prelude hiding (pred)
import Pretty ((<>), Associativity(InfixN, InfixR, InfixA), Doc, Expr, Fixity(Fixity), HasFixity(fixity),
               leafFixity, parenthesize, Pretty(pPrint), prettyShow, rootFixity, Side(LHS, RHS, Unary), text)
import Prop (foldPropositional, IsAtom, IsPropositional, JustLiteral, JustPropositional)
import Text.PrettyPrint (parens, braces, brackets, punctuate, comma, fcat, fsep, hsep, space)
#ifndef NOTESTS
import Data.Map as Map (empty, fromList)
import Data.Set as Set (fromList)
import Formulas (IsNegatable(..))
import Lit (foldLiteral')
import Prop (foldPropositional', PFormula)
import Test.HUnit
#endif

---------------
-- VARIABLES --
---------------

class (Ord v, IsString v, Pretty v, Show v) => IsVariable v where
    variant :: v -> Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.

-- | Return an infinite list of variations on v
variants :: IsVariable v => v -> [v]
variants v0 =
    loop Set.empty v0
    where loop s v = let v' = variant v s in v' : loop (Set.insert v s) v'

{-
showVariable :: IsVariable v => v -> String
showVariable v = "(fromString (" ++ show (show (prettyVariable v)) ++ "))"
-}

#ifndef NOTESTS
newtype V = V String deriving (Eq, Ord, Data, Typeable, Read, Show)

instance IsVariable String where
    variant v vs = if Set.member v vs then variant (v ++ "'") vs else v
    prefix pre s = pre ++ s
    -- prettyVariable = text

instance IsVariable V where
    variant v@(V s) vs = if Set.member v vs then variant (V (s ++ "'")) vs else v
    prefix pre (V s) = V (pre ++ s)
    -- prettyVariable (V s) = text s

instance IsString V where
    fromString = V

instance Show (Marked Expr V) where
    show (Mark (V s)) = show s

instance Pretty V where
    pPrint (V s) = text s
#endif

---------------
-- FUNCTIONS --
---------------

class (IsString function, Ord function, Pretty function, Show function) => IsFunction function

type Arity = Int

-- | Class of objects for which we can find a set of (function, arity) pairs.
class (IsFunction function, Ord function) => HasFunctions t function where
    funcs :: t -> Set (function, Arity)

instance HasFunctions t function => HasFunctions (Marked mk t) function where
    funcs = funcs . unMark'

#ifndef NOTESTS
-- | A simple type to use as the function parameter of Term, FOL, etc.
-- The only reason to use this instead of String is to get nicer
-- pretty printing.
newtype FName = FName String deriving (Eq, Ord, Show)

instance IsFunction FName

instance IsString FName where fromString = FName

instance Show (Marked Expr FName) where show (Mark (FName s)) = s

instance Pretty FName where pPrint (FName s) = text s
#endif

-----------
-- TERMS --
-----------

-- | Terms are built from variables and combined by functions to build the atoms of a formula.
class (Eq term, Ord term, Pretty term, Show term, IsVariable v, IsFunction function)
    => IsTerm term v function | term -> v function where
    vt :: v -> term
    -- ^ Build a term which is a variable reference.
    fApp :: function -> [term] -> term
    -- ^ Build a term by applying terms to an atomic function.  @f@
    -- (atomic function) is one of the type parameters, this package
    -- is mostly indifferent to its internal structure.
    foldTerm :: (v -> r) -> (function -> [term] -> r) -> term -> r
    -- ^ A fold for the term data type, which understands terms built
    -- from a variable and a term built from the application of a
    -- primitive function to other terms.

-- | Combine two terms if they are similar (i.e. two variables or
-- two function applications.)
zipTerms :: (IsTerm term1 v1 function1, IsTerm term2 v2 function2
            ) => (v1 -> v2 -> Maybe r) -> (function1 -> [term1] -> function2 -> [term2] -> Maybe r) -> term1 -> term2 -> Maybe r
zipTerms v ap t1 t2 =
    foldTerm v' ap' t1
    where
      v' v1 =      foldTerm     (v v1)   (\_ _ -> Nothing) t2
      ap' p1 ts1 = foldTerm (\_ -> Nothing) (\p2 ts2 -> if length ts1 == length ts2 then ap p1 ts1 p2 ts2 else Nothing)   t2

termFuncs :: IsTerm term v function => term -> Set (function, Arity)
termFuncs = foldTerm (\_ -> Set.empty) (\f ts -> Set.singleton (f, length ts))

-- | Convert between two instances of IsTerm
convertTerm :: (IsTerm term1 v1 f1, IsTerm term2 v2 f2) => (v1 -> v2) -> (f1 -> f2) -> term1 -> term2
convertTerm cv cf = foldTerm (vt . cv) (\f ts -> fApp (cf f) (map (convertTerm cv cf) ts))

prettyTerm :: (IsTerm term v function, Pretty v, Pretty function) => term -> Doc
prettyTerm = foldTerm pPrint prettyFunctionApply

prettyFunctionApply :: IsTerm term v function => function -> [term] -> Doc
prettyFunctionApply f [] = pPrint f
prettyFunctionApply f ts = pPrint f <> space <> brackets (hsep (punctuate comma (map prettyTerm ts)))

{-
showTerm :: (IsTerm term v function, Show function, Show v) => term -> String
showTerm = foldTerm (\v -> "vt " ++ show v) (\ fn ts -> show (prettyApply (text ("fApp (" ++ show fn ++ ")")) (text " ") (map (text . showTerm) ts)))
-- showTerm = foldTerm (\v -> "vt " ++ show v) (\ fn ts -> "fApp (" ++ show fn ++ ") [" ++ intercalate ", " (map showTerm ts) ++ "]")
-}

showTerm :: (IsTerm term v function, Pretty v, Pretty function) => term -> String
showTerm = foldTerm (\v -> "vt " <> show v) showFunctionApply

showFunctionApply :: IsTerm term v function => function -> [term] -> String
showFunctionApply f ts = "fApp (" <> show f <> ")" <> show (brackets (fsep (punctuate (comma <> space) (map (text . show) ts))))

#ifndef NOTESTS
data Term function v
    = Var v
    | FApply function [Term function v]
    deriving (Eq, Ord, Data, Typeable, Show)

{-
instance (IsVariable v, Show v, IsFunction function, Show function) => Show (Marked Expr (Term function v)) where
    show = showTerm . unMark'
-}

instance (IsFunction function, IsVariable v) => HasFunctions (Term function v) function where
    funcs = termFuncs

instance (IsFunction function, IsVariable v) => IsTerm (Term function v) v function where
    vt = Var
    fApp = FApply
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          FApply f ts -> fn f ts

instance (IsTerm (Term function v) v function) => Pretty (Term function v) where
    pPrint = prettyTerm

-- Example.
test00 :: Test
test00 = TestCase $ assertEqual "print an expression"
                                "sqrt [- [1, cos [power [+ [x, y], 2]]]]"
                                (prettyShow (fApp "sqrt" [fApp "-" [fApp "1" [],
                                                                     fApp "cos" [fApp "power" [fApp "+" [Var "x", Var "y"],
                                                                                               fApp "2" []]]]] :: Term FName V))
#endif

---------------
-- PREDICATE --
----------------

-- | A predicate is the thing we apply to a list of terms to get an
-- atom.  It doesn't have a Pretty superclass because we only render
-- it in combination with the argument terms.
class (Eq predicate, Ord predicate, Show predicate, IsString predicate, Pretty predicate, HasBoolean predicate) => IsPredicate predicate

---------------------------
-- ATOM (Atomic Formula) --
---------------------------

class (IsAtom atom, IsPredicate (PredOf atom), Ord (TermOf atom), Pretty (TermOf atom)) => HasApply atom where
    type PredOf atom
    type TermOf atom
    applyPredicate :: PredOf atom -> [(TermOf atom)] -> atom
    foldPredicate' :: (atom -> r) -> (PredOf atom -> [(TermOf atom)] -> r) -> atom -> r --- rename FoldAtom
    overterms :: ((TermOf atom) -> r -> r) -> r -> atom -> r
    onterms :: ((TermOf atom) -> (TermOf atom)) -> atom -> atom

-- | Atoms that have apply but do not support equate
class JustApply atom

foldPredicate :: (HasApply atom, JustApply atom) => (PredOf atom -> [TermOf atom] -> r) -> atom -> r
foldPredicate = foldPredicate' (error "JustApply failure")

-- | Pretty print prefix application of a predicate
prettyApply :: (IsPredicate predicate, IsTerm term v function) => predicate -> [term] -> Doc
prettyApply p ts = pPrint p <> brackets (fcat (punctuate (comma <> space) (map pPrint ts)))

-- | Implementation of 'overterms' for 'HasApply' types.
overtermsApply :: (HasApply atom, JustApply atom) => ((TermOf atom) -> r -> r) -> r -> atom -> r
overtermsApply f r0 = foldPredicate (\_ ts -> foldr f r0 ts)

-- | Implementation of 'onterms' for 'HasApply' types.
ontermsApply :: (HasApply atom, JustApply atom) => ((TermOf atom) -> (TermOf atom)) -> atom -> atom
ontermsApply f = foldPredicate (\p ts -> applyPredicate p (map f ts))

-- | Implementation of 'funcs' for 'HasApply' types
atomFuncs :: (HasApply atom, HasFunctions (TermOf atom) function) => atom -> Set (function, Arity)
atomFuncs = overterms (\term s -> Set.union (funcs term) s) mempty

-- | Zip two atoms if they are similar
zipPredicates :: (HasApply atom, JustApply atom) =>
                 (PredOf atom -> [((TermOf atom), (TermOf atom))] -> Maybe r)
              -> atom -> atom -> Maybe r
zipPredicates f atom1 atom2 =
    foldPredicate f' atom1
    where
      f' p1 ts1 = foldPredicate (\p2 ts2 ->
                                     if p1 /= p2 || length ts1 /= length ts2
                                     then Nothing
                                     else f p1 (zip ts1 ts2)) atom2

showApply :: (Show predicate, Show term) => predicate -> [term] -> String
showApply p ts = show (text "pApp " <> parens (text (show p)) <> brackets (fcat (punctuate (comma <> space) (map (text . show) ts))))

-- | Atoms that support equality must have HasApplyAndEquate instance
class HasApply atom => HasApplyAndEquate atom where
    equate :: TermOf atom -> TermOf atom -> atom
    foldEquate :: (TermOf atom -> TermOf atom -> r) -> (PredOf atom -> [TermOf atom] -> r) -> atom -> r
    -- prettyEquate :: forall term. Pretty term => predicate -> term -> term -> Doc

overtermsEq :: HasApplyAndEquate atom => (TermOf atom -> r -> r) -> r -> atom -> r
overtermsEq f r0 = foldEquate (\t1 t2 -> f t2 (f t1 r0)) (\_ ts -> foldr f r0 ts)

-- atom1 and atom2?
ontermsEq :: HasApplyAndEquate atom => (TermOf atom -> TermOf atom) -> atom -> atom
ontermsEq f = foldEquate (\t1 t2 -> equate (f t1) (f t2)) (\p ts -> applyPredicate p (map f ts))

-- | Zip two atoms that support equality
zipPredicatesEq :: forall atom r.
                   (HasApplyAndEquate atom) =>
                   (TermOf atom -> TermOf atom ->
                    TermOf atom -> TermOf atom -> Maybe r)
                -> (PredOf atom -> [(TermOf atom, TermOf atom)] -> Maybe r)
                -> atom -> atom -> Maybe r
zipPredicatesEq eq ap atom1 atom2 =
    foldEquate eq' ap' atom1
    where
      eq' l1 r1 = foldEquate (eq l1 r1) (\_ _ -> Nothing) atom2
      ap' p1 ts1 = foldEquate (\_ _ -> Nothing) (ap'' p1 ts1) atom2
      ap'' p1 ts1 p2 ts2 | p1 == p2 && length ts1 == length ts2 = ap p1 (zip ts1 ts2)
      ap'' _ _ _ _ = Nothing

isEquate :: HasApplyAndEquate atom => atom -> Bool
isEquate = foldEquate (\_ _ -> True) (\_ _ -> False)

prettyEquate :: IsTerm term v function => term -> term -> Doc
prettyEquate t1 t2 = pPrint t1 <> text "=" <> pPrint t2

showApplyAndEquate :: (HasApplyAndEquate atom, Show (TermOf atom)) => atom -> String
showApplyAndEquate atom = foldEquate showEquate showApply atom

showEquate :: Show term => term -> term -> String
showEquate t1 t2 = "(" ++ show t1 ++ ") .=. (" ++ show t2 ++ ")"

-- | Convert between two instances of HasApply
convertPredicate :: (HasApply atom1, JustApply atom1, HasApply atom2) => (PredOf atom1 -> PredOf atom2) -> (TermOf atom1 -> TermOf atom2) -> atom1 -> atom2
convertPredicate cp ct = foldPredicate (\p1 ts1 -> applyPredicate (cp p1) (map ct ts1))

convertPredicateEq :: (HasApplyAndEquate atom1, HasApplyAndEquate atom2) => (PredOf atom1 -> PredOf atom2) -> (TermOf atom1 -> TermOf atom2) -> atom1 -> atom2
convertPredicateEq cp ct = foldEquate (\t1 t2 -> equate (ct t1) (ct t2)) (\p1 ts1 -> applyPredicate (cp p1) (map ct ts1))

#ifndef NOTESTS

-- | This Predicate type includes an distinct Equals constructor, so
-- that we can use it to build an atoms with HasApplyAndEquate.
data Predicate
    = TP
    | FP
    | NamedPred String
    deriving (Eq, Ord, Data, Typeable, Show)

instance HasBoolean Predicate where
    fromBool True = TP
    fromBool False = FP
    asBool TP = Just True
    asBool FP = Just False
    asBool _ = Nothing

instance IsString Predicate where
    fromString "True" = error "bad predicate name: True"
    fromString "False" = error "bad predicate name: True"
    fromString "=" = error "bad predicate name: True"
    fromString s = NamedPred s

instance Pretty Predicate where
    pPrint TP = error "Use of True as a prefix predicate is prohibited"
    pPrint FP = error "Use of False as a prefix predicate is prohibited"
    pPrint (NamedPred "=") = error "Use of = as a predicate name is prohibited"
    pPrint (NamedPred "True") = error "Use of True as a predicate name is prohibited"
    pPrint (NamedPred "False") = error "Use of False as a predicate name is prohibited"
    pPrint (NamedPred s) = text s

{-
prettyApply :: Doc -> Doc -> [Doc] -> Doc
prettyApply p _ [] = p
prettyApply p sep ts = p <> sep <> brackets (hsep (punctuate comma ts))

prettyEquate :: Doc -> Doc -> Doc
prettyEquate a b = a <> text "=" <> b
-}

instance Pretty Predicate => IsPredicate Predicate {- where
    prettyPredicateApplication Equals [t1, t2] = prettyEquate (pPrint t1) (pPrint t2)
    prettyPredicateApplication Equals _ = error "prettyEquate Predicate - expected two argument terms"
    prettyPredicateApplication p@(NamedPredicate s) ts = maybe (prettyApply (text s) mempty (map pPrint ts)) prettyBool (asBool p) -}

instance Show (Marked Expr Predicate) where
    show (Mark TP) = "true"
    show (Mark FP) = "false"
    show (Mark (NamedPred s)) = "fromString " ++ show s

-- | First order logic formula atom type.
data FOL predicate term = R predicate [term] deriving (Eq, Ord, Data, Typeable, Show)

instance JustApply (FOL predicate term)

data FOLEQ predicate term = AP predicate [term] | Equals term term deriving (Eq, Ord, Data, Typeable, Show)

instance (IsPredicate predicate, IsTerm term v function) => IsAtom (FOL predicate term)

instance (IsPredicate predicate, IsTerm term v function) => IsAtom (FOLEQ predicate term)

instance (HasApply (FOL predicate term),
          JustApply (FOL predicate term), IsTerm term v function
         ) => Pretty (FOL predicate term) where
    pPrint = foldPredicate prettyApply

instance (HasApply (FOLEQ predicate term),
          HasApplyAndEquate (FOLEQ predicate term),
          IsTerm term v function) => Pretty (FOLEQ predicate term) where
    pPrint = foldEquate prettyEquate prettyApply

instance (IsPredicate predicate, IsTerm term v function) => HasApply (FOL predicate term) where
    type PredOf (FOL predicate term) = predicate
    type TermOf (FOL predicate term) = term
    applyPredicate = R
    foldPredicate' _ f (R p ts) = f p ts
    overterms f r (R _ ts) = foldr f r ts
    onterms f (R p ts) = R p (map f ts)

instance (IsPredicate predicate, IsTerm term v function) => HasApply (FOLEQ predicate term) where
    type PredOf (FOLEQ predicate term) = predicate
    type TermOf (FOLEQ predicate term) = term
    applyPredicate = AP
    foldPredicate' _ f (AP p ts) = f p ts
    foldPredicate' d _ x = d x
    overterms f r (AP _ ts) = foldr f r ts
    overterms f r (Equals t1 t2) = foldr f r [t1, t2]
    onterms f (AP p ts) = AP p (map f ts)
    onterms f (Equals t1 t2) = Equals (f t1) (f t2)

instance (IsPredicate predicate, IsTerm term v function,
          Show (Marked Expr predicate),
          Show (Marked Expr term)) => Show (Marked Expr (FOL predicate term)) where
    show = foldPredicate (\p ts -> showApply (Mark p :: Marked Expr predicate) (map Mark ts :: [Marked Expr term])) . unMark'

instance (IsPredicate predicate, IsTerm term v function,
          Show (Marked Expr predicate), Show (Marked Expr term)) => Show (Marked Expr (FOLEQ predicate term)) where
    show = foldEquate (\t1 t2 -> showEquate (Mark t1 :: Marked Expr term) (Mark t2 :: Marked Expr term))
                      (\p ts -> showApply (Mark p :: Marked Expr predicate) (map Mark ts :: [Marked Expr term])) . unMark'

instance (IsPredicate predicate, IsTerm term v function) => HasApplyAndEquate (FOLEQ predicate term) where
    equate lhs rhs = Equals lhs rhs
    foldEquate eq _ (Equals lhs rhs) = eq lhs rhs
    foldEquate _ ap (AP p ts) = ap p ts

instance (HasApply (FOL predicate term), HasFunctions term function) => HasFunctions (FOL predicate term) function where
    funcs = atomFuncs

instance (HasApply (FOLEQ predicate term), HasFunctions term function) => HasFunctions (FOLEQ predicate term) function where
    funcs = atomFuncs

instance HasFixity (FOL predicate term) where
    fixity _ = Fixity 6 InfixN

instance HasFixity (FOLEQ predicate term) where
    fixity _ = Fixity 6 InfixN
#endif

--------------
-- FORMULAS --
--------------

-- | Build a formula from a predicate and a list of terms.
pApp :: (IsFormula formula, atom ~ AtomOf formula, HasApply atom) => PredOf atom -> [TermOf atom] -> formula
pApp p args = atomic (applyPredicate p args)

-- | Build an equality formula from two terms.
(.=.) :: (IsFormula formula, atom ~ AtomOf formula, HasApplyAndEquate atom) => TermOf atom -> TermOf atom -> formula
a .=. b = atomic (equate a b)

infix 5 .=. -- , .!=., ≡, ≢

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

-- | Combine IsQuantified, HasApply, IsTerm
class (IsQuantified formula,
       HasApply (AtomOf formula),
       IsTerm term (VarOf formula) function,
       HasFunctions formula function,
       Pretty formula,
       atom ~ AtomOf formula,
       v ~ VarOf formula
      ) => IsFirstOrder formula atom predicate term v function

instance (IsQuantified formula, IsPropositional (Marked mk formula)) => IsQuantified (Marked mk formula) where
    type VarOf (Marked mk formula) = VarOf formula
    quant q v x = Mark $ quant q v (unMark' x)
    foldQuantified qu co ne tf at f = foldQuantified qu' co' ne' tf at (unMark' f)
        where qu' op v f' = qu op v (Mark f')
              ne' x = ne (Mark x)
              co' x op y = co (Mark x) op (Mark y)

instance IsFirstOrder formula atom predicate term v function => IsFirstOrder (Marked mk formula) atom predicate term v function

-- | Implementation of funcs for quantified formulas.
quantifiedFuncs :: forall formula function.
                   (IsQuantified formula, HasApply (AtomOf formula), {-, Ord function,
                    atom ~ (AtomOf formula), -}
                    HasFunctions (AtomOf formula) function
                   ) => formula -> Set (function, Arity)
quantifiedFuncs = foldQuantified qu co ne tf at
    where qu _ _ fm = quantifiedFuncs fm
          ne fm = quantifiedFuncs fm
          co lhs _ rhs = union (quantifiedFuncs lhs) (quantifiedFuncs rhs)
          tf _ = Set.empty
          at = (funcs :: AtomOf formula -> Set (function, Arity))

propositionalFuncs :: forall formula function.
                   (IsPropositional formula,
                    JustPropositional formula,
                    HasFunctions (AtomOf formula) function) => formula -> Set (function, Arity)
propositionalFuncs = foldPropositional co ne tf at
    where ne fm = propositionalFuncs fm
          co lhs _ rhs = union (propositionalFuncs lhs) (propositionalFuncs rhs)
          tf _ = Set.empty
          at = funcs

fixityQuantified :: forall formula. IsQuantified formula => formula -> Fixity
fixityQuantified fm =
    foldQuantified qu co ne tf at fm
    where
      qu _ _ _ = Fixity 9 InfixR
      ne _ = Fixity 5 InfixA
      co _ (:&:) _ = Fixity 4 InfixA
      co _ (:|:) _ = Fixity 3 InfixA
      co _ (:=>:) _ = Fixity 2 InfixR
      co _ (:<=>:) _ = Fixity 1 InfixA
      tf _ = Fixity 10 InfixN
      at = (fixity :: AtomOf formula -> Fixity)

prettyQuantified :: forall formula. IsQuantified formula => formula -> Doc
prettyQuantified fm0 =
    go rootFixity Unary fm0
    where
      go parentFixity side fm =
          parenthesize parens braces parentFixity fix side $ foldQuantified qu co ne tf at fm
          where
            fix = fixity fm
            qu (:!:) x p = text ("∀" ++ prettyShow x ++ ". ") <> go fix RHS p
            qu (:?:) x p = text ("∃" ++ prettyShow x ++ ". ") <> go fix RHS p
            ne f = text "¬" <> go fix Unary f
            co f (:&:) g = go fix LHS f <> text "∧" <> go fix RHS g
            co f (:|:) g = go fix LHS f <> text "∨" <> go fix RHS g
            co f (:=>:) g = go fix LHS f <> text "⇒" <> go fix RHS g
            co f (:<=>:) g = go fix LHS f <> text "⇔" <> go fix RHS g
            tf = pPrint
            at = (pPrint :: AtomOf formula -> Doc)

-- | For clarity, show methods fully parenthesize
showQuantified :: forall formula. (IsQuantified formula, HasFixity formula, Show (AtomOf formula), Ord (AtomOf formula)) => formula -> String
showQuantified fm0 =
    go rootFixity Unary fm0
    where
      go parentFixity side fm =
          parenthesize' parentFixity fix side $ foldQuantified qu co ne tf at fm
          where
            fix = fixity fm
            qu (:!:) x p = "for_all " ++ show x <> " " <> go fix RHS p
            qu (:?:) x p = "exists " ++ show x <> " " <> go fix RHS p
            ne f = "(.~.) (" <> go fix Unary f ++ ")" -- parenthesization of prefix operators is sketchy
            co f (:&:) g = go fix LHS f <> " .&. " <> go fix RHS g
            co f (:|:) g = go fix LHS f <> " .|. " <> go fix RHS g
            co f (:=>:) g = go fix LHS f <> " .=>. " <> go fix RHS g
            co f (:<=>:) g = go fix LHS f <> " .<=>. " <> go fix RHS g
            tf = show
            at = (show :: AtomOf formula -> String)
      parenthesize' _ _ _ fm = parenthesize (\s -> "(" <> s <> ")") (\s -> "{" <> s <> "}") leafFixity rootFixity Unary fm

#ifndef NOTESTS
data Formula v atom
    = F
    | T
    | Atom atom
    | Not (Formula v atom)
    | And (Formula v atom) (Formula v atom)
    | Or (Formula v atom) (Formula v atom)
    | Imp (Formula v atom) (Formula v atom)
    | Iff (Formula v atom) (Formula v atom)
    | Forall v (Formula v atom)
    | Exists v (Formula v atom)
    deriving (Eq, Ord, Data, Typeable, Read)

instance (HasFunctions atom function,
          HasApply atom,
          IsTerm (TermOf atom) v function)
    => HasFunctions (Formula v atom) function where
    funcs = quantifiedFuncs

instance (HasFunctions atom function,
          HasApply atom,
          IsTerm (TermOf atom) v function)
    => HasFunctions (PFormula atom) function where
    funcs = propositionalFuncs

instance (HasApply atom,
          IsTerm (TermOf atom) v function)
    => Pretty (Formula v atom) where
    pPrint = prettyQuantified

instance HasBoolean (Formula v atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance IsNegatable (Formula v atom) where
    naiveNegate = Not
    foldNegation' inverted normal (Not x) = foldNegation' normal inverted x
    foldNegation' _ normal x = normal x

instance IsCombinable (Formula v atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff
    foldCombination dj cj imp iff other fm =
        case fm of
          Or a b -> a `dj` b
          And a b -> a `cj` b
          Imp a b -> a `imp` b
          Iff a b -> a `iff` b
          _ -> other fm

-- The IsFormula instance for Formula
instance (HasApply atom, IsTerm (TermOf atom) v function, Ord v) => IsFormula (Formula v atom) where
    type AtomOf (Formula v atom) = atom
    atomic = Atom
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified

instance (IsFormula (Formula v atom), HasApply atom, IsTerm (TermOf atom) v function) => IsPropositional (Formula v atom) where
    foldPropositional' ho co ne tf at fm =
        case fm of
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          _ -> foldLiteral' ho ne tf at fm

instance forall atom v. (IsPropositional (Formula v atom), IsVariable v, IsAtom atom) => IsQuantified (Formula v atom) where
    type VarOf (Formula v atom) = v
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldQuantified qu _co _ne _tf _at (Forall v fm) = qu (:!:) v fm
    foldQuantified qu _co _ne _tf _at (Exists v fm) = qu (:?:) v fm
    foldQuantified _qu co ne tf at fm =
        foldPropositional' (\_ -> error "IsQuantified Formula") co ne tf at fm

-- Build a Haskell expression for this formula
instance IsQuantified (Formula v atom) => Show (Formula v atom) where
    show = showQuantified

-- Precedence information for Formula
instance IsQuantified (Formula v atom) => HasFixity (Formula v atom) where
    fixity = fixityQuantified

instance (HasApply atom, IsTerm (TermOf atom) v function) => IsLiteral (Formula v atom) where
    foldLiteral' ho ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> ne p
          _ -> ho fm
#endif

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

for_all :: IsQuantified formula => VarOf formula -> formula -> formula
for_all = quant (:!:)
exists :: IsQuantified formula => VarOf formula -> formula -> formula
exists = quant (:?:)

-- Irrelevant, because these are always used as prefix operators, never as infix.
infixr 9 ∀, ∃

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: IsQuantified formula => VarOf formula -> formula -> formula
(∀) = for_all
(∃) :: IsQuantified formula => VarOf formula -> formula -> formula
(∃) = exists

#ifndef NOTESTS
-- | Concrete types for use in unit tests.
type MyTerm1 = Term FName V -- MyTerm1 has no Skolem functions
type MyAtom1 = FOL Predicate MyTerm1
type MyAtom2 = FOLEQ Predicate MyTerm1
type MyFormula1 = Formula V MyAtom1
type MyFormula2 = Formula V MyAtom2

instance IsFirstOrder MyFormula1 MyAtom1 Predicate MyTerm1 V FName
instance IsFirstOrder MyFormula2 MyAtom2 Predicate MyTerm1 V FName

instance JustApply MyAtom2
#endif

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (IsFormula formula, atom ~ AtomOf formula, HasApply atom) => ((TermOf atom) -> (TermOf atom)) -> formula -> formula
onformula f = onatoms (atomic . onterms f)

onatomsQuantified :: IsQuantified formula => (AtomOf formula -> formula) -> formula -> formula
onatomsQuantified f fm =
    foldQuantified qu co ne tf at fm
    where
      qu op v p = quant op v (onatomsQuantified f p)
      ne p = (.~.) (onatomsQuantified f p)
      co p op q = binop (onatomsQuantified f p) op (onatomsQuantified f q)
      tf flag = fromBool flag
      at x = f x

overatomsQuantified :: IsQuantified fof => (AtomOf fof -> r -> r) -> fof -> r -> r
overatomsQuantified f fof r0 =
    foldQuantified qu co ne (const r0) (flip f r0) fof
    where
      qu _ _ fof' = overatomsQuantified f fof' r0
      ne fof' = overatomsQuantified f fof' r0
      co p _ q = overatomsQuantified f p (overatomsQuantified f q r0)

{-
(* Trivial example of "x + y < z".                                           *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
Atom(R("<",[Fn("+",[Var "x"; Var "y"]); Var "z"]));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Parsing of terms.                                                         *)
(* ------------------------------------------------------------------------- *)

let is_const_name s = forall numeric (explode s) or s = "nil";;

let rec parse_atomic_term vs inp =
  match inp with
    [] -> failwith "term expected"
  | "("::rest -> parse_bracketed (parse_term vs) ")" rest
  | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
  | f::"("::")"::rest -> Fn(f,[]),rest
  | f::"("::rest ->
      papply (fun args -> Fn(f,args))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | a::rest ->
      (if is_const_name a & not(mem a vs) then Fn(a,[]) else Var a),rest

and parse_term vs inp =
  parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
    (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
       (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
          (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
             (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                   (parse_atomic_term vs)))))) inp;;

let parset = make_parser (parse_term []);;

(* ------------------------------------------------------------------------- *)
(* Parsing of formulas.                                                      *)
(* ------------------------------------------------------------------------- *)

let parse_infix_atom vs inp =
  let tm,rest = parse_term vs inp in
  if exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then
        papply (fun tm' -> Atom(R(hd rest,[tm;tm'])))
               (parse_term vs (tl rest))
  else failwith "";;

let parse_atom vs inp =
  try parse_infix_atom vs inp with Failure _ ->
  match inp with
  | p::"("::")"::rest -> Atom(R(p,[])),rest
  | p::"("::rest ->
      papply (fun args -> Atom(R(p,args)))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | p::rest when p <> "(" -> Atom(R(p,[])),rest
  | _ -> failwith "parse_atom";;

let parse = make_parser
  (parse_formula (parse_infix_atom,parse_atom) []);;

(* ------------------------------------------------------------------------- *)
(* Set up parsing of quotations.                                             *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse;;

let secondary_parser = parset;;

{-
(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<(forall x. x < 2 ==> 2 * x <= 3) \/ false>>;;

<<|2 * x|>>;;
END_INTERACTIVE;;
-}

(* ------------------------------------------------------------------------- *)
(* Printing of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec print_term prec fm =
  match fm with
    Var x -> print_string x
  | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
  | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
  | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
  | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
  | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
  | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
  | Fn(f,args) -> print_fargs f args

and print_fargs f args =
  print_string f;
  if args = [] then () else
   (print_string "(";
    open_box 0;
    print_term 0 (hd args); print_break 0 0;
    do_list (fun t -> print_string ","; print_break 0 0; print_term 0 t)
            (tl args);
    close_box();
    print_string ")")

and print_infix_term isleft oldprec newprec sym p q =
  if oldprec > newprec then (print_string "("; open_box 0) else ();
  print_term (if isleft then newprec else newprec+1) p;
  print_string sym;
  print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
  print_term (if isleft then newprec+1 else newprec) q;
  if oldprec > newprec then (close_box(); print_string ")") else ();;

let printert tm =
  open_box 0; print_string "<<|";
  open_box 0; print_term 0 tm; close_box();
  print_string "|>>"; close_box();;

#install_printer printert;;

(* ------------------------------------------------------------------------- *)
(* Printing of formulas.                                                     *)
(* ------------------------------------------------------------------------- *)

let print_atom prec (R(p,args)) =
  if mem p ["="; "<"; "<="; ">"; ">="] & length args = 2
  then print_infix_term false 12 12 (" "^p) (el 0 args) (el 1 args)
  else print_fargs p args;;

let print_fol_formula = print_qformula print_atom;;

#install_printer print_fol_formula;;

(* ------------------------------------------------------------------------- *)
(* Examples in the main text.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
<<forall x y. exists z. x < z /\ y < z>>;;

<<~(forall x. P(x)) <=> exists y. ~P(y)>>;;
END_INTERACTIVE;;
-}

-- | Specify the domain of a formula interpretation, and how to
-- interpret its functions and predicates.
data Interp function predicate d
    = Interp { domain :: [d]
             , funcApply :: function -> [d] -> d
             , predApply :: predicate -> [d] -> Bool
             , eqApply :: d -> d -> Bool }

-- | The hold function computes the value of a formula for a finite domain.
class FiniteInterpretation a function predicate v dom where
    holds :: Interp function predicate dom -> Map v dom -> a -> Bool

-- | Implementation of holds for IsQuantified formulas.
holdsQuantified :: forall formula function predicate dom.
                   (IsQuantified formula,
                    FiniteInterpretation (AtomOf formula) function predicate (VarOf formula) dom,
                    FiniteInterpretation formula function predicate (VarOf formula) dom) =>
                   Interp function predicate dom -> Map (VarOf formula) dom -> formula -> Bool
holdsQuantified m v fm =
    foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = and (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- >>= return . any (== True)
      qu (:?:) x p = or (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- return . all (== True)?
      ne p = not (holds m v p)
      co p (:&:) q = (holds m v p) && (holds m v q)
      co p (:|:) q = (holds m v p) || (holds m v q)
      co p (:=>:) q = not (holds m v p) || (holds m v q)
      co p (:<=>:) q = (holds m v p) == (holds m v q)
      tf x = x
      at = (holds m v :: AtomOf formula -> Bool)

-- | Implementation of holds for IsPropositional formulas.
holdsPropositional :: (IsPropositional pf, JustPropositional pf,
                       FiniteInterpretation (AtomOf pf) function predicate (VarOf pf) dom,
                       FiniteInterpretation pf function predicate (VarOf pf) dom) =>
                      Interp function predicate dom -> Map (VarOf pf) dom -> pf -> Bool
holdsPropositional m v fm =
    foldPropositional co ne tf at fm
    where
      co p (:&:) q = (holds m v p) && (holds m v q)
      co p (:|:) q = (holds m v p) || (holds m v q)
      co p (:=>:) q = not (holds m v p) || (holds m v q)
      co p (:<=>:) q = (holds m v p) == (holds m v q)
      ne p = not (holds m v p)
      tf x = x
      at x = holds m v x

-- | Implementation of holds for IsLiteral formulas.
holdsLiteral :: (IsLiteral lit, JustLiteral lit,
                 FiniteInterpretation (AtomOf lit) function predicate (VarOf lit) dom,
                 FiniteInterpretation lit function predicate (VarOf lit) dom) =>
                Interp function predicate dom -> Map (VarOf lit) dom -> lit -> Bool
holdsLiteral m v fm =
    foldLiteral ne tf at fm
    where
      ne p = not (holds m v p)
      tf x = x
      at x = holds m v x

holdsAtom :: (HasApply atom, JustApply atom, IsTerm (TermOf atom) v function, Eq dom) =>
             Interp function (PredOf atom) dom -> Map v dom -> atom -> Bool
holdsAtom m v at = foldPredicate (\r args -> predApply m r (map (termval m v) args)) at

holdsAtomEq :: (HasApplyAndEquate atom, IsTerm (TermOf atom) v function, Eq dom) =>
               Interp function (PredOf atom) dom -> Map v dom -> atom -> Bool
holdsAtomEq m v at = foldEquate (\t1 t2 -> eqApply m (termval m v t1) (termval m v t2))
                                (\r args -> predApply m r (map (termval m v) args)) at

termval :: (IsTerm term v function, Show v) => Interp function predicate r -> Map v r -> term -> r
termval m v tm =
    foldTerm (\x -> fromMaybe (error ("Undefined variable: " ++ show x)) (Map.lookup x v))
             (\f args -> funcApply m f (map (termval m v) args)) tm

-- | Examples of particular interpretations.
bool_interp :: Interp FName Predicate Bool
bool_interp =
    Interp [False, True] func pred (==)
    where
      func f [] | f == fromString "False" = False
      func f [] | f == fromString "True" = True
      func f [x,y] | f == fromString "+" = x /= y
      func f [x,y] | f == fromString "*" = x && y
      func f _ = error ("bool_interp - uninterpreted function: " ++ show f)
      pred p _ = error ("bool_interp - uninterpreted predicate: " ++ show p)

mod_interp :: Int -> Interp FName Predicate Int
mod_interp n =
    Interp [0..(n-1)] func pred (==)
    where
      func f [] | f == fromString "0" = 0
      func f [] | f == fromString "1" = 1 `mod` n
      func f [x,y] | f == fromString "+" = (x + y) `mod` n
      func f [x,y] | f == fromString "*" = (x * y) `mod` n
      func f _ = error ("mod_interp - uninterpreted function: " ++ show f)
      pred p _ = error ("mod_interp - uninterpreted predicate: " ++ show p)

{-
START_INTERACTIVE;;
holds bool_interp undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 2) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

holds (mod_interp 3) undefined <<forall x. (x = 0) \/ (x = 1)>>;;

let fm = <<forall x. ~(x = 0) ==> exists y. x * y = 1>>;;

filter (fun n -> holds (mod_interp n) undefined fm) (1--45);;

holds (mod_interp 3) undefined <<(forall x. x = 0) ==> 1 = 0>>;;
holds (mod_interp 3) undefined <<forall x. x = 0 ==> 1 = 0>>;;
END_INTERACTIVE;;
-}

#ifndef NOTESTS
instance Eq dom => FiniteInterpretation MyFormula2 FName Predicate V dom where
    holds = holdsQuantified
instance Eq dom => FiniteInterpretation MyAtom2 FName Predicate V dom where
    holds = holdsAtomEq

test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds bool_interp (Map.empty :: Map V Bool) (for_all "x" (vt "x" .=. fApp "False" [] .|. vt "x" .=. fApp "True" []) :: MyFormula2)
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: MyFormula2)
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: MyFormula2)
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) (Map.empty :: Map V Int) fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: MyFormula2
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) (Map.empty :: Map V Int) ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: MyFormula2)
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) (Map.empty :: Map V Int) (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: MyFormula2)
          expected = False
#endif

-- Free variables in terms and formulas.

-- | Find the free variables in a formula.
fv :: (atom ~ AtomOf formula, IsFirstOrder formula atom (PredOf atom) (TermOf atom) (VarOf formula) function) => formula -> Set (VarOf formula)
fv fm =
    foldQuantified qu co ne tf at fm
    where
      qu _ x p = difference (fv p) (singleton x)
      ne p = fv p
      co p _ q = union (fv p) (fv q)
      tf _ = Set.empty
      at = fva

fvp :: (IsPropositional formula,
        JustPropositional formula,
        atom ~ AtomOf formula,
        HasApply atom,
        IsTerm (TermOf atom) (VarOf formula) function
       ) => formula -> Set (VarOf formula)
fvp fm = overatoms (\a s -> Set.union (fva a) s) fm mempty

fvl :: (IsLiteral formula,
        JustLiteral formula,
        atom ~ AtomOf formula,
        HasApply atom,
        IsTerm (TermOf atom) (VarOf formula) f
       ) => formula -> Set (VarOf formula)
fvl fm = overatoms (\a s -> Set.union (fva a) s) fm mempty

fva :: (HasApply atom, IsTerm (TermOf atom) v function) => atom -> Set v
fva = overterms (\t s -> Set.union (fvt t) s) mempty

-- | Find the variables in a formula.
var :: (atom ~ AtomOf formula, IsFirstOrder formula atom (PredOf atom) (TermOf atom) (VarOf formula) function) => formula -> Set (VarOf formula)
var fm = overatoms (\a s -> Set.union (fva a) s) fm mempty

-- | Find the variables in a 'Term'.
fvt :: IsTerm term v function => term -> Set v
fvt tm = foldTerm singleton (\_ args -> unions (map fvt args)) tm

-- | Universal closure of a formula.
generalize :: (atom ~ (AtomOf formula), IsFirstOrder formula atom (PredOf atom) (TermOf atom) (VarOf formula) function) => formula -> formula
generalize fm = Set.fold for_all fm (fv fm)

#ifndef NOTESTS
test07 :: Test
test07 = TestCase $ assertEqual "variant 1 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["y", "z"]) :: V
          expected = "x"
test08 :: Test
test08 = TestCase $ assertEqual "variant 2 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "y"]) :: V
          expected = "x'"
test09 :: Test
test09 = TestCase $ assertEqual "variant 3 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "x'"]) :: V
          expected = "x''"
#endif

-- | Substitution in formulas, with variable renaming.
subst :: (atom ~ AtomOf formula, IsFirstOrder formula atom (PredOf atom) (TermOf atom) (VarOf formula) function) =>
         Map (VarOf formula) (TermOf atom) -> formula -> formula
subst subfn fm =
    foldQuantified qu co ne tf at fm
    where
      qu (:!:) x p = substq subfn for_all x p
      qu (:?:) x p = substq subfn exists x p
      ne p = (.~.) (subst subfn p)
      co p (:&:) q = (subst subfn p) .&. (subst subfn q)
      co p (:|:) q = (subst subfn p) .|. (subst subfn q)
      co p (:=>:) q = (subst subfn p) .=>. (subst subfn q)
      co p (:<=>:) q = (subst subfn p) .<=>. (subst subfn q)
      tf False = false
      tf True = true
      at = atomic . asubst subfn

-- | Substitution within terms.
tsubst :: IsTerm term v function => Map v term -> term -> term
tsubst sfn tm =
    foldTerm (\x -> fromMaybe tm (Map.lookup x sfn))
             (\f args -> fApp f (map (tsubst sfn) args))
             tm

-- | Substitution within a Literal
lsubst :: (IsLiteral lit, atom ~ AtomOf lit, HasApply atom, IsTerm (TermOf atom) (VarOf lit) function) =>
         Map (VarOf lit) (TermOf atom) -> lit -> lit
lsubst subfn fm =
    foldLiteral ne fromBool at fm
    where
      ne p = (.~.) (lsubst subfn p)
      at = atomic . asubst subfn

-- | Substitution within atoms.
asubst :: (HasApply atom, IsTerm (TermOf atom) v function) => Map v (TermOf atom) -> atom -> atom
asubst sfn a = onterms (tsubst sfn) a

-- | Substitution within quantifiers
substq :: (atom ~ AtomOf formula, IsFirstOrder formula atom (PredOf atom) (TermOf atom) (VarOf formula) function) =>
          Map (VarOf formula) (TermOf atom)
       -> (VarOf formula -> formula -> formula)
       -> VarOf formula
       -> formula
       -> formula
substq subfn qu x p =
  let x' = if setAny (\y -> Set.member x (fvt(tryApplyD subfn y (vt y))))
                     (difference (fv p) (singleton x))
           then variant x (fv (subst (undefine x subfn) p)) else x in
  qu x' (subst ((x |-> vt x') subfn) p)

#ifndef NOTESTS
-- Examples.

test10 :: Test
test10 =
    let [x, x', y] = [vt "x", vt "x'", vt "y"]
        fm = for_all "x" ((x .=. y)) :: MyFormula2
        expected = for_all "x'" (x' .=. x) :: MyFormula2 in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

test11 :: Test
test11 =
    let [x, x', x'', y] = [vt "x", vt "x'", vt "x''", vt "y"]
        fm = (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x')))) :: MyFormula2
        expected = for_all "x'" (for_all "x''" ((x' .=. x) .=>. ((x' .=. x'')))) :: MyFormula2 in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

testFOL :: Test
testFOL = TestLabel "FOL" (TestList [test00, test01, test02, test03, test04,
                                     test05, test06, test07, test08, test09,
                                     test10, test11])
#endif
