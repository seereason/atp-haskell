-- | Basic stuff for first order logic.
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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module FOL
    ( -- * Variables
      IsVariable(variant, prefix, prettyVariable), variants, showVariable
    -- * Functions
    , IsFunction
    -- * Terms
    , IsTerm(vt, fApp, foldTerm, zipTerms), convertTerm
    -- * Predicates
    , IsPredicate(prettyPredicateApplication), HasEquals(equals, isEquals)
    -- * Atoms
    , HasPredicate(applyPredicate, foldPredicate), convertPredicate, zipPredicates, pApp
    , HasEquality(applyEquals, foldEquals'), (.=.), foldEquals, zipEquals
    -- * Quantifiers
    , Quant((:!:), (:?:))
    -- Formula
    , IsQuantified(quant, foldQuantified), for_all, exists, (∀), (∃)
    , IsFirstOrder
    , zipFirstOrder
    , fixityFirstOrder
    , convertFirstOrder
    , propositionalFromFirstOrder
    , literalFromFirstOrder
    , onatomsFirstOrder
    , overatomsFirstOrder
    , onformula
    -- * Semantics
    , Interp
    , termval
    , holds
    , bool_interp
    , mod_interp
    -- * Free Variables
    , var
    , fv
    , fva
    , fvt
    , generalize
    -- * Substitution
    , subst, substq, asubst, tsubst, lsubst
#ifndef NOTESTS
    -- * Instances
    , V(V)
    , FName(FName)
    , Term(Var, FApply)
    , Predicate(NamedPredicate, Equals)
    , FOL(R)
    , Formula(F, T, Atom, Not, And, Or, Imp, Iff, Forall, Exists)
    , MyFormula1
    -- * Tests
    , tests
#endif
    ) where

import Data.Data (Data)
import Data.List (intercalate, intersperse)
import Data.Map as Map (empty, fromList, insert, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Set as Set (difference, empty, fold, fromList, insert, member, Set, singleton, union, unions)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Prelude hiding (pred)

import Formulas (BinOp(..), Combination(..), HasBoolean(..), IsNegatable(..), IsCombinable(..), IsFormula(..),
                 (.~.), true, false, onatoms, binop)
import Lib (setAny, tryApplyD, undefine, (|->))
import Lit (IsLiteral(foldLiteral))
import Prop (IsPropositional(foldPropositional))

#ifndef NOTESTS
import Test.HUnit
import Pretty (Doc, Associativity(InfixN, InfixR, InfixL, InfixA), HasFixity(fixity), Fixity(Fixity), parenthesize, Pretty(pPrint), prettyShow, text, rootFixity, Side(LHS, RHS, Unary), (<>))
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
    prettyVariable :: v -> Doc
    -- ^ Pretty print a variable

-- | Return an infinite list of variations on v
variants :: IsVariable v => v -> [v]
variants v0 =
    iter' Set.empty v0
    where iter' s v = let v' = variant v s in v' : iter' (Set.insert v s) v'

showVariable :: IsVariable v => v -> String
showVariable v = "(fromString (" ++ show (show (prettyVariable v)) ++ "))"

#ifndef NOTESTS
newtype V = V String deriving (Eq, Ord, Read, Data, Typeable)

instance IsVariable String where
    variant v vs = if Set.member v vs then variant (v ++ "'") vs else v
    prefix pre s = pre ++ s
    prettyVariable = text

instance IsVariable V where
    variant v@(V s) vs = if Set.member v vs then variant (V (s ++ "'")) vs else v
    prefix pre (V s) = V (pre ++ s)
    prettyVariable (V s) = text s

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pPrint (V s) = text s
#endif

---------------
-- FUNCTIONS --
---------------

class (IsString function, Ord function, Pretty function) => IsFunction function

#ifndef NOTESTS
-- | A simple type to use as the function parameter of Term, FOL, etc.
-- The only reason to use this instead of String is to get nicer
-- pretty printing.
newtype FName = FName String deriving (Eq, Ord)

instance IsFunction FName

instance IsString FName where fromString = FName

instance Show FName where show (FName s) = s

instance Pretty FName where pPrint (FName s) = text s
#endif

-----------
-- TERMS --
-----------

-- | Terms are built from variables and combined by functions to build the atoms of a formula.
class (Eq term, Ord term, Pretty term, IsVariable v, IsFunction function) => IsTerm term v function | term -> v function where
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
    zipTerms :: (v -> v -> Maybe r) -> (function -> [term] -> function -> [term] -> Maybe r) -> term -> term -> Maybe r
    -- ^ Combine two terms if they are similar (i.e. two variables or
    -- two function applications.)

-- | Convert between two instances of IsTerm
convertTerm :: (IsTerm term1 v1 f1, IsTerm term2 v2 f2) => (v1 -> v2) -> (f1 -> f2) -> term1 -> term2
convertTerm cv cf = foldTerm (vt . cv) (\f ts -> fApp (cf f) (map (convertTerm cv cf) ts))

showTerm :: (IsTerm term v function, Show function, Show v) => term -> String
showTerm = foldTerm (\v -> "vt " ++ show v) (\ fn ts -> "fApp " ++ show fn ++ "[" ++ intercalate ", " (map showTerm ts) ++ "]")

#ifndef NOTESTS
data Term function v
    = Var v
    | FApply function [Term function v]
    deriving (Eq, Ord, Data, Typeable)

instance (IsVariable v, Show v, IsFunction function, Show function) => Show (Term function v) where
    show = showTerm

instance (IsFunction function, IsVariable v) => IsTerm (Term function v) v function where
    vt = Var
    fApp = FApply
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          FApply f ts -> fn f ts
    zipTerms v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FApply f1 ts1, FApply f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing

instance (Pretty function, Pretty v) => Pretty (Term function v) where
    pPrint (Var v) = pPrint v
    pPrint (FApply fn []) = pPrint fn
    pPrint (FApply fn args) = pPrint fn <> text " [" <> mconcat (intersperse (text ", ") (map pPrint args)) <> text "]"

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

-- | A predicate is closely associated with a term type, especially
-- when pretty printing.
class (IsString predicate, Eq predicate, Ord predicate, Pretty predicate, Show predicate,
       Ord term, Pretty term) => IsPredicate predicate term where
    prettyPredicateApplication :: predicate -> [term] -> Doc

-- | Class of predicates that have an equality predicate.
class HasEquals predicate where
    equals :: predicate
    isEquals :: predicate -> Bool

#ifndef NOTESTS
-- | This Predicate type includes an distinct Equals constructor, so
-- that we can build an HasEquals instance for it.
data Predicate
    = NamedPredicate String
    | Equals
    deriving (Eq, Ord, Data, Typeable, Show)

instance (IsFunction function, IsVariable v) => IsPredicate Predicate (Term function v) where
    prettyPredicateApplication Equals [a, b] =
        pPrint a <> text "=" <> pPrint b
    prettyPredicateApplication Equals _ts =
        error "Arity mismatch for equals predicate"
    prettyPredicateApplication p ts =
        pPrint p <> text "[" <> mconcat (intersperse (text ", ") (map pPrint ts)) <> text "]"

-- | Predicates with a 'HasEquals' instance are needed whenever the
-- '.=.' combiner is used.
instance HasEquals Predicate where
    equals = Equals
    isEquals Equals = True
    isEquals _ = False

instance IsString Predicate where
    fromString = NamedPredicate

instance Pretty Predicate where
    pPrint Equals = text "="
    pPrint (NamedPredicate "=") = error "Use of = as a predicate name is prohibited"
    pPrint (NamedPredicate s) = text s
#endif

----------
-- ATOM --
----------

class (IsPredicate predicate term) => HasPredicate atom predicate term | atom -> predicate term where
    applyPredicate :: predicate -> [term] -> atom
    foldPredicate :: (predicate -> [term] -> r) -> atom -> r

zipPredicates :: HasPredicate atom predicate term =>
                 (predicate -> [(term, term)] -> Maybe r)
              -> atom -> atom -> Maybe r
zipPredicates f atom1 atom2 =
    foldPredicate f' atom1
    where
      f' p1 ts1 = foldPredicate (\p2 ts2 ->
                                     if p1 /= p2 || length ts1 /= length ts2
                                     then Nothing
                                     else f p1 (zip ts1 ts2)) atom2

-- | A predicate that HasEquals can be used to build an
-- atom/predicate/term combo that HasEquality.
class (HasPredicate atom predicate term, HasEquals predicate) => HasEquality atom predicate term where
    applyEquals :: term -> term -> atom
    foldEquals' :: (term -> term -> r) -> atom -> Maybe r

foldEquals :: HasEquality atom predicate term => (predicate -> [term] -> r) -> (term -> term -> r) -> atom -> r
foldEquals ap eq atom = fromMaybe (foldPredicate ap atom) (foldEquals' eq atom)

zipEquals :: HasEquality atom predicate term =>
             (predicate -> predicate -> [(term, term)] -> Maybe r)
          -> (term -> term -> term -> term -> Maybe r)
          -> atom -> atom -> Maybe r
zipEquals ap eq atom1 atom2 =
    foldEquals ap' eq' atom1
    where
      ap' p ts = foldEquals (ap'' p ts) (\_ _ -> Nothing) atom2
      ap'' _p1 ts1 _p2 ts2 | length ts1 /= length ts2 = Nothing
      ap'' p1 ts1 p2 ts2 = ap p1 p2 (zip ts1 ts2)
      eq' lhs1 rhs1 = foldEquals (\_ _ -> Nothing) (eq lhs1 rhs1) atom2

-- | Convert between two instances of HasPredicate
convertPredicate :: (HasPredicate atom1 p1 t1, HasPredicate atom2 p2 t2) => (p1 -> p2) -> (t1 -> t2) -> atom1 -> atom2
convertPredicate cp ct = foldPredicate (\p1 ts1 -> applyPredicate (cp p1) (map ct ts1))

#ifndef NOTESTS
-- | First order logic formula atom type.
data FOL predicate term = R predicate [term] deriving (Eq, Ord, Data, Typeable)

instance IsPredicate predicate term => Pretty (FOL predicate term) where
    pPrint = foldPredicate prettyPredicateApplication

{-
instance (IsPredicate predicate term, Pretty term, Ord term) => Pretty (FOL predicate term) where
    pPrint = foldPredicate prettyPredicateApplication
-}

instance (IsPredicate predicate term, Show predicate, Show term) => Show (FOL predicate term) where
    show (R p ts) = "applyPredicate " ++ show p ++ " [" ++ intercalate ", " (map show ts) ++ "]"

instance (IsPredicate predicate term, Pretty term, Ord term) => HasPredicate (FOL predicate term) predicate term where
    applyPredicate = R
    foldPredicate f (R p ts) = f p ts

instance IsPredicate Predicate term => HasEquality (FOL Predicate term) Predicate term where
    applyEquals lhs rhs = applyPredicate Equals [lhs, rhs]
    foldEquals' f (R Equals [lhs, rhs]) = Just (f lhs rhs)
    foldEquals' _ _ = Nothing

instance HasFixity (FOL predicate term) where
    fixity _ = Fixity 6 InfixN
#endif

----------------
-- QUANTIFIER --
----------------

data Quant
    = (:!:) -- ^ for_all
    | (:?:) -- ^ exists
    deriving (Eq, Ord, Data, Typeable, Show)

--------------
-- FORMULAE --
--------------

-- | Use a predicate to combine some terms into a formula.
pApp :: (IsFormula formula atom, HasPredicate atom predicate term) => predicate -> [term] -> formula
pApp p args = atomic $ applyPredicate p args

-- | Apply the equals predicate to two terms and build a formula.
(.=.) :: (IsFormula formula atom, HasEquality atom predicate term) => term -> term -> formula
a .=. b = atomic (applyEquals a b)

infix 5 .=. -- , .!=., ≡, ≢

class (IsPropositional formula atom, IsVariable v) => IsQuantified formula atom v | formula -> atom v where
    quant :: Quant -> v -> formula -> formula
    foldQuantified :: (Quant -> v -> formula -> r)
                   -> (Combination formula -> r)
                   -> (Bool -> r)
                   -> (atom -> r)
                   -> formula -> r

-- |Combine IsFirstOrder, HasPredicate, IsTerm
class (IsQuantified formula atom v, HasPredicate atom predicate term, IsTerm term v function, Show v
      ) => IsFirstOrder formula atom predicate term v function

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

instance (Ord atom, Pretty atom, HasPredicate atom predicate term, IsTerm term v function,
          IsVariable v, HasFixity atom, Pretty v) => Pretty (Formula v atom) where
    pPrint = prettyFormula rootFixity Unary

instance HasBoolean (Formula v atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance (Ord v, Ord atom) => IsNegatable (Formula v atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (Ord v, Ord atom) => IsCombinable (Formula v atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff

instance (Ord atom, HasFixity atom, Pretty atom, HasPredicate atom predicate term, IsTerm term v function) => IsQuantified (Formula v atom) atom v where
    quant (:!:) = Forall
    quant (:?:) = Exists
    foldQuantified qu _co _tf _at (Forall v fm) = qu (:!:) v fm
    foldQuantified qu _co _tf _at (Exists v fm) = qu (:?:) v fm
    foldQuantified _qu co tf at fm = foldPropositional co tf at fm

-- Build a Haskell expression for this formula
instance (Show atom, Show v) => Show (Formula v atom) where
    show F = "false"
    show T = "true"
    show (Atom atom) = show atom
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"
    show (Forall v f) = "(for_all " ++ show v ++ " " ++ show f ++ ")"
    show (Exists v f) = "(exists " ++ show v ++ " " ++ show f ++ ")"

-- Precedence information for Formula
instance HasFixity atom => HasFixity (Formula v atom) where
    fixity T = Fixity 10 InfixN
    fixity F = Fixity 10 InfixN
    fixity (Atom a) = fixity a
    fixity (Not _) = Fixity 5 InfixN
    fixity (And _ _) = Fixity 4 InfixA
    fixity (Or _ _) = Fixity 3 InfixA
    fixity (Imp _ _) = Fixity 2 InfixR
    fixity (Iff _ _) = Fixity 1 InfixA
    fixity (Forall _ _) = Fixity 9 InfixR
    fixity (Exists _ _) = Fixity 9 InfixR

-- The IsFormula instance for Formula
instance (HasFixity atom, Pretty atom, HasPredicate atom predicate term, IsTerm term v function, Ord v, Ord atom) => IsFormula (Formula v atom) atom where
    atomic = Atom
    overatoms f fm b =
      case fm of
        Atom a -> f a b
        Not p -> overatoms f p b
        And p q -> overatoms f p (overatoms f q b)
        Or p q -> overatoms f p (overatoms f q b)
        Imp p q -> overatoms f p (overatoms f q b)
        Iff p q -> overatoms f p (overatoms f q b)
        Forall _x p -> overatoms f p b
        Exists _x p -> overatoms f p b
        _ -> b
    onatoms f fm =
      case fm of
        Atom a -> f a
        Not p -> Not (onatoms f p)
        And p q -> And (onatoms f p) (onatoms f q)
        Or p q -> Or (onatoms f p) (onatoms f q)
        Imp p q -> Imp (onatoms f p) (onatoms f q)
        Iff p q -> Iff (onatoms f p) (onatoms f q)
        Forall x p -> Forall x (onatoms f p)
        Exists x p -> Exists x (onatoms f p)
        _ -> fm
    prettyFormula pfix side fm =
      parenthesize pfix fix side $ foldQuantified qu co tf at fm
        where
          fix = fixity fm
          qu (:!:) x p = text ("∀" ++ prettyShow x ++ ". ") <> prettyFormula fix RHS p
          qu (:?:) x p = text ("∃" ++ prettyShow x ++ ". ") <> prettyFormula fix RHS p
          co ((:~:) f) = text "¬" <> prettyFormula fix Unary f
          co (BinOp f (:&:) g) = prettyFormula fix LHS f <> text "∧" <> prettyFormula fix RHS g
          co (BinOp f (:|:) g) = prettyFormula fix LHS f <> text "∨" <> prettyFormula fix RHS g
          co (BinOp f (:=>:) g) = prettyFormula fix LHS f <> text "⇒" <> prettyFormula fix RHS g
          co (BinOp f (:<=>:) g) = prettyFormula fix LHS f <> text "⇔" <> prettyFormula fix RHS g
          tf = pPrint
          at = pPrint

instance (Ord atom, HasFixity atom, Pretty atom, HasPredicate atom predicate term, IsTerm term v function) => IsPropositional (Formula v atom) atom where
    foldPropositional co tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> co ((:~:) p)
          And p q -> co (BinOp p (:&:) q)
          Or p q -> co (BinOp p (:|:) q)
          Imp p q -> co (BinOp p (:=>:) q)
          Iff p q -> co (BinOp p (:<=>:) q)
          -- Although every instance of IsFirstOrder is also an
          -- instance of IsPropositional, we see here that it is
          -- an error to use foldPropositional (IsPropositional's
          -- only method) on a Formula that has quantifiers.
          Forall _ _ -> error $ "foldPropositional used on Formula with a quantifier: " ++ prettyShow fm
          Exists _ _ -> error $ "foldPropositional used on Formula with a quantifier: " ++ prettyShow fm

instance (Ord atom, HasFixity atom, Pretty atom, HasPredicate atom predicate term, IsTerm term v function) => IsLiteral (Formula v atom) atom where
    foldLiteral ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not p -> ne p
          And _ _ -> error $ "foldLiteral used on Formula with a binop: " ++ prettyShow fm
          Or _ _ -> error $ "foldLiteral used on Formula with a binop: " ++ prettyShow fm
          Imp _ _ -> error $ "foldLiteral used on Formula with a binop: " ++ prettyShow fm
          Iff _ _ -> error $ "foldLiteral used on Formula with a binop: " ++ prettyShow fm
          Forall _ _ -> error $ "foldLiteral used on Formula with a quantifier: " ++ prettyShow fm
          Exists _ _ -> error $ "foldLiteral used on Formula with a quantifier: " ++ prettyShow fm
#endif

-- | Combine two formulas if they are similar.
zipFirstOrder :: IsQuantified formula atom v =>
                 (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
              -> (Combination formula -> Combination formula -> Maybe r)
              -> (Bool -> Bool -> Maybe r)
              -> (atom -> atom -> Maybe r)
              -> formula -> formula -> Maybe r
zipFirstOrder qu co tf at fm1 fm2 =
    foldQuantified qu' co' tf' at' fm1
    where
      qu' op1 v1 p1 = foldQuantified (qu op1 v1 p1) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      co' c1 = foldQuantified (\ _ _ _ -> Nothing) (co c1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldQuantified (\ _ _ _ -> Nothing) (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' atom1 = foldQuantified (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at atom1) fm2

fixityFirstOrder :: (HasFixity atom, IsQuantified formula atom v) => formula -> Fixity
fixityFirstOrder formula =
    foldQuantified qu co tf at formula
    where
      qu _ _ _ = Fixity 10 InfixN
      co ((:~:) _) = Fixity 5 InfixN
      co (BinOp _ (:&:) _) = Fixity 4 InfixL
      co (BinOp _ (:|:) _) = Fixity 3 InfixL
      co (BinOp _ (:=>:) _) = Fixity 2 InfixR
      co (BinOp _ (:<=>:) _) = Fixity 1 InfixL
      tf _ = Fixity 10 InfixN
      at = fixity

-- | Use foldPropositional to convert any instance of
-- IsPropositional to any other by specifying the result type.
convertFirstOrder :: forall f1 a1 v1 f2 a2 v2.
                     (IsQuantified f1 a1 v1, IsQuantified f2 a2 v2) =>
                     (a1 -> a2) -> (v1 -> v2) -> f1 -> f2
convertFirstOrder ca cv f1 =
    foldQuantified qu co tf at f1
    where
      qu :: Quant -> v1 -> f1 -> f2
      qu (:!:) x p = for_all (cv x) (convertFirstOrder ca cv p :: f2)
      qu (:?:) x p = exists (cv x) (convertFirstOrder ca cv p :: f2)
      co :: Combination f1 -> f2
      co ((:~:) p) = (.~.) (convertFirstOrder ca cv p)
      co (BinOp p (:&:) q) = convertFirstOrder ca cv p .&. convertFirstOrder ca cv q
      co (BinOp p (:|:) q) = convertFirstOrder ca cv p .|. convertFirstOrder ca cv q
      co (BinOp p (:=>:) q) = convertFirstOrder ca cv p .=>. convertFirstOrder ca cv q
      co (BinOp p (:<=>:) q) = convertFirstOrder ca cv p .<=>. convertFirstOrder ca cv q
      tf :: Bool -> f2
      tf = fromBool
      at :: a1 -> f2
      at = atomic . ca

-- | Convert any first order formula to a propositional formula.  If
-- we encounter a quantifier an error is raised.
propositionalFromFirstOrder :: (IsQuantified fof atom1 v, IsPropositional pf atom2) => (atom1 -> atom2) -> fof -> pf
propositionalFromFirstOrder ca fm =
    foldQuantified qu co fromBool (atomic . ca) fm
    where
      qu _ _ _ = error "propositionalFromFirstOrder: found quantifier"
      co ((:~:) p) = (.~.) (propositionalFromFirstOrder ca p)
      co (BinOp p (:&:) q) = propositionalFromFirstOrder ca p .&. propositionalFromFirstOrder ca q
      co (BinOp p (:|:) q) = propositionalFromFirstOrder ca p .|. propositionalFromFirstOrder ca q
      co (BinOp p (:=>:) q) = propositionalFromFirstOrder ca p .=>. propositionalFromFirstOrder ca q
      co (BinOp p (:<=>:) q) = propositionalFromFirstOrder ca p .<=>. propositionalFromFirstOrder ca q

literalFromFirstOrder :: (IsQuantified fof atom1 v, IsLiteral lit atom2) => (atom1 -> atom2) -> fof -> lit
literalFromFirstOrder ca fm =
    foldQuantified qu co fromBool (atomic . ca) fm
    where
      qu _ _ _ = error "literalFromFirstOrder: found quantifier"
      co ((:~:) p) = (.~.) (literalFromFirstOrder ca p)
      co _ = error "literalFromFirstOrder: found binary operator"

for_all :: IsQuantified formula atom v => v -> formula -> formula
for_all = quant (:!:)
exists :: IsQuantified formula atom v => v -> formula -> formula
exists = quant (:?:)

-- Irrelevant, because these are always used as prefix operators, never as infix.
infixr 9 ∀, ∃

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: IsQuantified formula atom v => v -> formula -> formula
(∀) = for_all
(∃) :: IsQuantified formula atom v => v -> formula -> formula
(∃) = exists

#ifndef NOTESTS
-- | Concrete types for use in unit tests.
type MyTerm = Term FName V
type MyAtom = FOL Predicate MyTerm
type MyFormula1 = Formula V MyAtom -- MyFormula is in Skolem, this one has no Equality predicate

instance IsFirstOrder MyFormula1 MyAtom Predicate MyTerm V FName
#endif

-- | Special case of applying a subfunction to the top *terms*.
onformula :: (IsFormula formula r, HasPredicate r predicate term) => (term -> term) -> formula -> formula
onformula f = onatoms (foldPredicate (\p a -> atomic $ applyPredicate p (map f a)))

-- | Apply a function to the atoms, otherwise keeping structure.  This
-- can generally be used as the onatoms method of IsFormula.
onatomsFirstOrder :: forall formula atom v. IsQuantified formula atom v => (atom -> formula) -> formula -> formula
onatomsFirstOrder f fm =
    foldQuantified qu co tf at fm
    where
      qu op v p = quant op v (onatomsFirstOrder f p)
      co ((:~:) p) = onatomsFirstOrder f p
      co (BinOp p op q) = binop (onatomsFirstOrder f p) op (onatomsFirstOrder f q)
      tf flag = fromBool flag
      at x = f x

-- | Formula analog of list iterator "itlist".
overatomsFirstOrder :: forall fof atom v r. IsQuantified fof atom v => (atom -> r -> r) -> fof -> r -> r
overatomsFirstOrder f fof r0 =
        foldQuantified qu co (const r0) (flip f r0) fof
        where
          qu _ _ fof' = overatomsFirstOrder f fof' r0
          co ((:~:) fof') = overatomsFirstOrder f fof' r0
          co (BinOp p _ q) = overatomsFirstOrder f p (overatomsFirstOrder f q r0)

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

-- | Semantics, implemented of course for finite domains only.
holds :: IsFirstOrder formula atom predicate term v function =>
         Interp function predicate dom -> Map v dom -> formula -> Bool
holds m v fm =
    foldQuantified qu co tf at fm
    where
      qu (:!:) x p = and (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- >>= return . any (== True)
      qu (:?:) x p = or (map (\a -> holds m (Map.insert x a v) p) (domain m)) -- return . all (== True)?
      co ((:~:) p) = not (holds m v p)
      co (BinOp p (:&:) q) = (holds m v p) && (holds m v q)
      co (BinOp p (:|:) q) = (holds m v p) || (holds m v q)
      co (BinOp p (:=>:) q) = not (holds m v p) || (holds m v q)
      co (BinOp p (:<=>:) q) = (holds m v p) == (holds m v q)
      tf x = x
      at = foldPredicate (\r args -> predApply m r (map (termval m v) args))

-- | Specify the domain of a formula interpretation, and how to
-- interpret its functions and predicates.
data Interp function predicate d
    = Interp { domain :: [d]
             , funcApply :: function -> [d] -> d
             , predApply :: predicate -> [d] -> Bool }

termval :: (IsTerm term v function, Show v) => Interp function predicate r -> Map v r -> term -> r
termval m v tm =
    foldTerm (\x -> fromMaybe (error ("Undefined variable: " ++ show x)) (Map.lookup x v))
             (\f args -> funcApply m f (map (termval m v) args)) tm

-- | Examples of particular interpretations.
bool_interp :: (IsFunction function, Show function, Show predicate, HasEquals predicate) =>
               Interp function predicate Bool
bool_interp =
    Interp [False, True] func pred
    where
      func f [] | f == fromString "False" = False
      func f [] | f == fromString "True" = True
      func f [x,y] | f == fromString "+" = not(x == y)
      func f [x,y] | f == fromString "*" = x && y
      func f _ = error ("bool_interp - uninterpreted function: " ++ show f)
      pred p [x,y] | isEquals p = x == y
      pred p _ = error ("bool_interp - uninterpreted predicate: " ++ show p)

mod_interp :: (IsFunction function, Show function, Show predicate, HasEquals predicate) =>
              Int -> Interp function predicate Int
mod_interp n =
    Interp [0..(n-1)] func pred
    where
      func f [] | f == fromString "0" = 0
      func f [] | f == fromString "1" = 1 `mod` n
      func f [x,y] | f == fromString "+" = (x + y) `mod` n
      func f [x,y] | f == fromString "*" = (x * y) `mod` n
      func f _ = error ("mod_interp - uninterpreted function: " ++ show f)
      pred p [x,y] | isEquals p = x == y
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
test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds bool_interp Map.empty (for_all  "x" (vt "x" .=. fApp "False" [] .|. vt "x" .=. fApp "True" []) :: MyFormula1)
          expected = True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (mod_interp 2) Map.empty (for_all "x" (vt "x" .=. (fApp "0" []) .|. vt "x" .=. (fApp "1" [])) :: MyFormula1)
          expected = True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: MyFormula1)
          expected = False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filter (\ n -> holds (mod_interp n) Map.empty fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: MyFormula1
          expected = [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: MyFormula1)
          expected = True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (mod_interp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: MyFormula1)
          expected = False
#endif

-- Free variables in terms and formulas.

-- | Find the free variables in a formula.
#if 0
fv :: (IsFormula formula atom, HasPredicate atom predicate term,  IsTerm term v function) => formula -> Set v
fv fm = overatoms (\a s -> foldPredicate (\_ args -> unions (s : map fvt args)) a) fm Set.empty
#else
fv :: IsFirstOrder formula atom predicate term v function => formula -> Set v
fv fm =
    foldQuantified qu co tf at fm
    where
      qu _ x p = difference (fv p) (singleton x)
      co ((:~:) p) = fv p
      co (BinOp p _ q) = union (fv p) (fv q)
      tf _ = Set.empty
      at = foldPredicate (\_ args -> unions (map fvt args))
#endif

fva :: (HasEquality atom predicate term, IsTerm term v function) => atom -> Set v
fva = foldEquals (\_ args -> unions (map fvt args)) (\lhs rhs -> union (fvt lhs) (fvt rhs))

-- | Find the variables in a formula.
#if 0
var :: (IsFormula formula atom, HasPredicate atom predicate term, IsTerm term v function) => formula -> Set v
var fm = overatoms (\a s -> foldPredicate (\_ args -> unions (s : map fvt args)) a) fm Set.empty
#else
var :: IsFirstOrder formula atom predicate term v function => formula -> Set v
var fm =
    foldQuantified qu co tf at fm
    where
      qu _ x p = Set.insert x (var p)
      co ((:~:) p) = var p
      co (BinOp p _ q) = union (var p) (var q)
      tf _ = Set.empty
      at = foldPredicate (\_ args -> unions (map fvt args))
#endif

-- | Find the variables in a 'Term'.
fvt :: IsTerm term v function => term -> Set v
fvt tm = foldTerm singleton (\_ args -> unions (map fvt args)) tm

-- | Universal closure of a formula.
generalize :: IsFirstOrder formula atom predicate term v function => formula -> formula
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
subst :: IsFirstOrder formula atom predicate term v function =>
         Map v term -> formula -> formula
subst subfn fm =
    foldQuantified qu co tf at fm
    where
      qu (:!:) x p = substq subfn for_all x p
      qu (:?:) x p = substq subfn exists x p
      co ((:~:) p) = (.~.) (subst subfn p)
      co (BinOp p (:&:) q) = (subst subfn p) .&. (subst subfn q)
      co (BinOp p (:|:) q) = (subst subfn p) .|. (subst subfn q)
      co (BinOp p (:=>:) q) = (subst subfn p) .=>. (subst subfn q)
      co (BinOp p (:<=>:) q) = (subst subfn p) .<=>. (subst subfn q)
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
lsubst :: (IsLiteral lit atom, HasPredicate atom predicate term, IsTerm term v function) =>
         Map v term -> lit -> lit
lsubst subfn fm =
    foldLiteral ne fromBool at fm
    where
      ne p = (.~.) (lsubst subfn p)
      at = atomic . asubst subfn

-- | Substitution within atoms.
asubst :: (HasPredicate atom predicate term, IsTerm term v function) => Map v term -> atom -> atom
asubst sfn a = foldPredicate (\p ts -> applyPredicate p (map (tsubst sfn) ts)) a

-- | Substitution within quantifiers
substq :: IsFirstOrder formula atom predicate term v function =>
          Map v term
       -> (v -> formula -> formula)
       -> v
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
        fm = for_all "x" ((x .=. y)) :: MyFormula1
        expected = for_all "x'" (x' .=. x) :: MyFormula1 in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

test11 :: Test
test11 =
    let [x, x', x'', y] = [vt "x", vt "x'", vt "x''", vt "y"]
        fm = (for_all "x" (for_all "x'" ((x .=. y) .=>. (x .=. x')))) :: MyFormula1
        expected = for_all "x'" (for_all "x''" ((x' .=. x) .=>. ((x' .=. x'')))) :: MyFormula1 in
    TestCase $ assertEqual ("subst (\"y\" |=> Var \"x\") " ++ prettyShow fm ++ " (p. 134)")
                           expected
                           (subst (Map.fromList [("y", x)]) fm)

tests :: Test
tests = TestLabel "FOL" $
        TestList [test00, test01, test02, test03, test04,
                  test05, test06, test07, test08, test09,
                  test10, test11]
#endif
