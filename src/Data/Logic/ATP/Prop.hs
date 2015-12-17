-- | Basic stuff for propositional logic: datatype, parsing and
-- printing.  'IsPropositional' is a subclass of 'IsLiteral' of
-- formula types that support binary combinations.

{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Logic.ATP.Prop
    (
    -- * Propositional formulas
      IsPropositional((.|.), (.&.), (.<=>.), (.=>.), foldPropositional', foldCombination)
    , BinOp(..), binop
    , (⇒), (==>), (⊃), (→)
    , (⇔), (<=>), (↔), (<==>)
    , (∧), (·)
    , (∨)
    , foldPropositional
    , zipPropositional
    , convertPropositional
    , convertToPropositional
    , precedencePropositional
    , associativityPropositional
    , prettyPropositional
    , showPropositional
    , onatomsPropositional
    , overatomsPropositional
    -- * Restricted propositional formula class
    , JustPropositional
    -- * Interpretation of formulas.
    , eval
    , atoms
    -- * Truth Tables
    , TruthTable(TruthTable)
    , onallvaluations
    , truthTable
    -- * Tautologies and related concepts
    , tautology
    , unsatisfiable
    , satisfiable
    -- * Substitution
    , psubst
    -- * Dualization
    , dual
    -- * Simplification
    , psimplify
    , psimplify1
    -- * Normal forms
    , nnf
    , nenf
    , list_conj
    , list_disj
    , mk_lits
    , allsatvaluations
    , dnfSet
    , purednf
    , simpdnf
    , rawdnf
    , dnf
    , purecnf
    , simpcnf
    , cnf'
    , cnf_
    , trivial
    -- * Instance
    , Prop(P, pname)
    , PFormula(F, T, Atom, Not, And, Or, Imp, Iff)
    -- * Tests
    , testProp
    ) where

import Data.Foldable as Foldable (null)
import Data.Function (on)
import Data.Data (Data)
import Data.List as List (groupBy, intercalate, map, sortBy)
import Data.Logic.ATP.Formulas (atom_union, fromBool, IsAtom,
                                IsFormula(AtomOf, asBool, true, false, atomic, overatoms, onatoms), prettyBool)
import Data.Logic.ATP.Lib ((|=>), distrib, fpf, setAny)
import Data.Logic.ATP.Lit ((.~.), (¬), convertLiteral, convertToLiteral, IsLiteral(foldLiteral', naiveNegate, foldNegation),
                           JustLiteral, LFormula, negate, positive, )
import Data.Logic.ATP.Pretty (Associativity(InfixN, InfixR, InfixA), Doc, HasFixity(precedence, associativity),
                              Precedence, Pretty(pPrint, pPrintPrec), prettyShow, Side(Top, LHS, RHS, Unary), testParen, text,
                              notPrec, andPrec, orPrec, impPrec, iffPrec, leafPrec, boolPrec)
import Data.Map.Strict as Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, fromList, intersection, isProperSubsetOf, map,
                        minView, partition, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Prelude hiding (negate, null)
import Text.PrettyPrint.HughesPJClass (maybeParens, PrettyLevel, vcat)
import Test.HUnit

-- |A type class for propositional logic.  If the type we are writing
-- an instance for is a zero-order (aka propositional) logic type
-- there will generally by a type or a type parameter corresponding to
-- atom.  For first order or predicate logic types, it is generally
-- easiest to just use the formula type itself as the atom type, and
-- raise errors in the implementation if a non-atomic formula somehow
-- appears where an atomic formula is expected (i.e. as an argument to
-- atomic or to the third argument of foldPropositional.)
class IsLiteral formula => IsPropositional formula where
    -- | Disjunction/OR
    (.|.) :: formula -> formula -> formula
    -- | Conjunction/AND.  @x .&. y = (.~.) ((.~.) x .|. (.~.) y)@
    (.&.) :: formula -> formula -> formula
    -- | Equivalence.  @x .<=>. y = (x .=>. y) .&. (y .=>. x)@
    (.<=>.) :: formula -> formula -> formula
    -- | Implication.  @x .=>. y = ((.~.) x .|. y)@
    (.=>.) :: formula -> formula -> formula

    -- | A fold function that distributes different sorts of formula
    -- to its parameter functions, one to handle binary operators, one
    -- for negations, and one for atomic formulas.  See examples of its
    -- use to implement the polymorphic functions below.
    foldPropositional' :: (formula -> r)                     -- ^ fold on some higher order formula
                       -> (formula -> BinOp -> formula -> r) -- ^ fold on a binary operation formula.  Functions
                                                             -- of this type can be constructed using 'binop'.
                       -> (formula -> r)                     -- ^ fold on a negated formula
                       -> (Bool -> r)                        -- ^ fold on a boolean formula
                       -> (AtomOf formula -> r)              -- ^ fold on an atomic formula
                       -> formula -> r
    -- | An alternative fold function for binary combinations of formulas
    foldCombination :: (formula -> r) -- other
                    -> (formula -> formula -> r) -- disjunction
                    -> (formula -> formula -> r) -- conjunction
                    -> (formula -> formula -> r) -- implication
                    -> (formula -> formula -> r) -- equivalence
                    -> formula -> r

-- | Implication synonyms.  Note that if the -XUnicodeSyntax option is
-- turned on the operator ⇒ can not be declared/used as a function -
-- it becomes a reserved special character used in type signatures.
(⇒), (⊃), (==>), (→) :: IsPropositional formula => formula -> formula -> formula
(⇒) = (.=>.)
(⊃) = (.=>.)
(==>) = (.=>.)
(→) = (.=>.)
infixr 3 .=>., ⇒, ⊃, ==>, →

-- | If-and-only-if synonyms
(<=>), (<==>), (⇔), (↔) :: IsPropositional formula => formula -> formula -> formula
(<=>) = (.<=>.)
(<==>) = (.<=>.)
(⇔) = (.<=>.)
(↔) = (.<=>.)
infixl 2 .<=>., <=>, <==>, ⇔, ↔

-- | And/conjunction synonyms
(∧), (·) :: IsPropositional formula => formula -> formula -> formula
(∧) = (.&.)
(·) = (.&.)
infixl 5 .&., ∧, ·

-- | Or/disjunction synonyms
(∨) :: IsPropositional formula => formula -> formula -> formula
(∨) = (.|.)
infixl 4 .|., ∨

-- | Deconstruct a 'JustPropositional' formula.
foldPropositional :: JustPropositional pf =>
                     (pf -> BinOp -> pf -> r) -- ^ fold on a binary operation formula
                  -> (pf -> r)                -- ^ fold on a negated formula
                  -> (Bool -> r)              -- ^ fold on a boolean formula
                  -> (AtomOf pf -> r)         -- ^ fold on an atomic formula
                  -> pf -> r
foldPropositional = foldPropositional' (error "JustPropositional failure")

-- | This type is used to construct the first argument of 'foldPropositional'.
data BinOp
    = (:<=>:)
    | (:=>:)
    | (:&:)
    | (:|:)
    deriving (Eq, Ord, Data, Typeable, Show, Enum, Bounded)

-- | Combine formulas with a 'BinOp', for use building the first
-- argument of 'foldPropositional'.
binop :: IsPropositional formula => formula -> BinOp -> formula -> formula
binop f1 (:<=>:) f2 = f1 .<=>. f2
binop f1 (:=>:) f2 = f1 .=>. f2
binop f1 (:&:) f2 = f1 .&. f2
binop f1 (:|:) f2 = f1 .|. f2

-- | Combine two 'JustPropositional' formulas if they are similar.
zipPropositional :: (JustPropositional pf1, JustPropositional pf2) =>
                    (pf1 -> BinOp -> pf1 -> pf2 -> BinOp -> pf2 -> Maybe r) -- ^ Combine two binary operation formulas
                 -> (pf1 -> pf2 -> Maybe r)                                 -- ^ Combine two negated formulas
                 -> (Bool -> Bool -> Maybe r)                               -- ^ Combine two boolean formulas
                 -> (AtomOf pf1 -> AtomOf pf2 -> Maybe r)                   -- ^ Combine two atomic formulas
                 -> pf1 -> pf2 -> Maybe r                                   -- ^ Result is Nothing if the formulas don't unify
zipPropositional co ne tf at fm1 fm2 =
    foldPropositional co' ne' tf' at' fm1
    where
      co' l1 op1 r1 = foldPropositional (co l1 op1 r1) (\_ -> Nothing) (\_ -> Nothing) (\_ -> Nothing) fm2
      ne' x1 = foldPropositional (\_ _ _ -> Nothing)     (ne x1)     (\_ -> Nothing) (\_ -> Nothing) fm2
      tf' x1 = foldPropositional (\_ _ _ -> Nothing) (\_ -> Nothing)     (tf x1)     (\_ -> Nothing) fm2
      at' a1 = foldPropositional (\_ _ _ -> Nothing) (\_ -> Nothing) (\_ -> Nothing)     (at a1)     fm2

-- | Convert any instance of 'JustPropositional' to any 'IsPropositional' formula.
convertPropositional :: (JustPropositional pf1, IsPropositional pf2) =>
                        (AtomOf pf1 -> AtomOf pf2) -- ^ Convert an atomic formula
                     -> pf1 -> pf2
convertPropositional ca pf =
    foldPropositional co ne tf (atomic . ca) pf
    where
      co p (:&:) q = (convertPropositional ca p) .&. (convertPropositional ca q)
      co p (:|:) q = (convertPropositional ca p) .|. (convertPropositional ca q)
      co p (:=>:) q = (convertPropositional ca p) .=>. (convertPropositional ca q)
      co p (:<=>:) q = (convertPropositional ca p) .<=>. (convertPropositional ca q)
      ne p = (.~.) (convertPropositional ca p)
      tf = fromBool

-- | Convert any instance of 'IsPropositional' to a 'JustPropositional' formula.  Typically the
-- ho (higher order) argument calls error if it encounters something it can't handle.
convertToPropositional :: (IsPropositional formula, JustPropositional pf) =>
                          (formula -> pf)               -- ^ Convert a higher order formula
                       -> (AtomOf formula -> AtomOf pf) -- ^ Convert an atomic formula
                       -> formula -> pf
convertToPropositional ho ca fm =
    foldPropositional' ho co ne tf (atomic . ca) fm
    where
      co p (:&:) q = (convertToPropositional ho ca p) .&. (convertToPropositional ho ca q)
      co p (:|:) q = (convertToPropositional ho ca p) .|. (convertToPropositional ho ca q)
      co p (:=>:) q = (convertToPropositional ho ca p) .=>. (convertToPropositional ho ca q)
      co p (:<=>:) q = (convertToPropositional ho ca p) .<=>. (convertToPropositional ho ca q)
      ne p = (.~.) (convertToPropositional ho ca p)
      tf = fromBool

-- | Implementation of 'precedence' for any 'JustPropostional' type.
precedencePropositional ::JustPropositional pf => pf -> Precedence
precedencePropositional = foldPropositional co (\_ -> notPrec) (\_ -> boolPrec) precedence
    where
      co _ (:&:) _ = andPrec
      co _ (:|:) _ = orPrec
      co _ (:=>:) _ = impPrec
      co _ (:<=>:) _ = iffPrec

associativityPropositional :: JustPropositional pf => pf -> Associativity
associativityPropositional = foldPropositional co (const InfixA) (const InfixN) associativity
    where
      co _ (:&:) _ = InfixA
      co _ (:|:) _ = InfixA
      co _ (:=>:) _ = InfixR
      co _ (:<=>:) _ = InfixA -- yes, InfixA: (a<->b)<->c == a<->(b<->c)

-- | Implementation of 'pPrint' for any 'JustPropostional' type.
prettyPropositional :: forall pf. JustPropositional pf =>
                       Side -> PrettyLevel -> Rational -> pf -> Doc
prettyPropositional side l r fm =
    maybeParens (testParen side r (precedence fm) (associativity fm)) $ foldPropositional co ne tf at fm
    where
      co :: pf -> BinOp -> pf -> Doc
      co p (:&:) q = prettyPropositional LHS l (precedence fm) p <> text "∧" <>  prettyPropositional RHS l (precedence fm) q
      co p (:|:) q = prettyPropositional LHS l (precedence fm) p <> text "∨" <> prettyPropositional RHS l (precedence fm) q
      co p (:=>:) q = prettyPropositional LHS l (precedence fm) p <> text "⇒" <> prettyPropositional RHS l (precedence fm) q
      co p (:<=>:) q = prettyPropositional LHS l (precedence fm) p <> text "⇔" <> prettyPropositional RHS l (precedence fm) q
      ne p = text "¬" <> prettyPropositional Unary l (precedence fm) p
      tf x = prettyBool x
      at x = pPrintPrec l r x

-- | Implementation of 'show' for any 'JustPropositional' type.  For clarity, show methods fully parenthesize
showPropositional :: JustPropositional pf => Side -> Int -> pf -> ShowS
showPropositional side parentPrec fm =
    showParen (testParen side parentPrec (precedence fm) (associativity fm)) $ foldPropositional co ne tf at fm
    where
      co p (:&:) q = showPropositional LHS (precedence fm) p . showString " .&. " . showPropositional RHS (precedence fm) q
      co p (:|:) q = showPropositional LHS (precedence fm) p . showString " .|. " . showPropositional RHS (precedence fm) q
      co p (:=>:) q = showPropositional LHS (precedence fm) p . showString " .=>. " . showPropositional RHS (precedence fm) q
      co p (:<=>:) q = showPropositional LHS (precedence fm) p . showString " .<=>. " . showPropositional RHS (precedence fm) q
      ne p = showString "(.~.) " . showPropositional Unary (succ (precedence fm)) p
      tf x = showsPrec (precedence fm) x
      at x = showString "atomic " . showsPrec (precedence fm) x

-- | Implementation of 'onatoms' for any 'JustPropositional' type.
onatomsPropositional :: JustPropositional pf => (AtomOf pf -> AtomOf pf) -> pf -> pf
onatomsPropositional f fm =
    foldPropositional co ne tf at fm
    where
      co p op q = binop (onatomsPropositional f p) op (onatomsPropositional f q)
      ne p = (.~.) (onatomsPropositional f p)
      tf flag = fromBool flag
      at x = atomic (f x)

-- | Implementation of 'overatoms' for any 'JustPropositional' type.
overatomsPropositional :: JustPropositional pf => (AtomOf pf -> r -> r) -> pf -> r -> r
overatomsPropositional f fof r0 =
    foldPropositional co ne (const r0) (flip f r0) fof
    where
      co p _ q = overatomsPropositional f p (overatomsPropositional f q r0)
      ne fof' = overatomsPropositional f fof' r0

-- | An instance of IsPredicate.
data Prop = P {pname :: String} deriving (Eq, Ord)

-- Because of the IsString instance, the Show instance can just be a String.
instance Show Prop where
    show (P {pname = s}) = show s

instance IsAtom Prop

-- Allows us to say "q" instead of P "q" or P {pname = "q"}
instance IsString Prop where
    fromString = P

instance Pretty Prop where
    pPrint = text . pname

instance HasFixity Prop where
    precedence (P _) = leafPrec

-- | An instance of IsPropositional.
data PFormula atom
    = F
    | T
    | Atom atom
    | Not (PFormula atom)
    | And (PFormula atom) (PFormula atom)
    | Or (PFormula atom) (PFormula atom)
    | Imp (PFormula atom) (PFormula atom)
    | Iff (PFormula atom) (PFormula atom)
    deriving (Eq, Ord, Read, Data, Typeable)

-- Build a Haskell expression for this formula
instance (IsPropositional (PFormula atom), Show atom) => Show (PFormula atom) where
    showsPrec p x = showPropositional Top p x -- . showString " :: PFormula Prop"

instance IsAtom atom => HasFixity (PFormula atom) where
    precedence = precedencePropositional
    associativity = associativityPropositional

instance IsAtom atom => IsFormula (PFormula atom) where
    type AtomOf (PFormula atom) = atom
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    true = T
    false = F
    atomic = Atom
    overatoms = overatomsPropositional
    onatoms = onatomsPropositional

instance IsAtom atom => IsPropositional (PFormula atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff
    foldPropositional' _ co ne tf at fm =
        case fm of
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          _ -> foldLiteral' (error "IsPropositional PFormula") ne tf at fm
    foldCombination other dj cj imp iff fm =
        case fm of
          Or a b -> a `dj` b
          And a b -> a `cj` b
          Imp a b -> a `imp` b
          Iff a b -> a `iff` b
          _ -> other fm

instance IsAtom atom => IsLiteral (PFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x
    foldLiteral' ho ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not l -> ne l
          _ -> ho fm

instance IsAtom atom => Pretty (PFormula atom) where
    pPrintPrec = prettyPropositional Top

-- | Class that indicates a formula type *only* supports Propositional
-- features - it has no way to represent quantifiers.
class IsPropositional formula => JustPropositional formula

instance IsAtom atom => JustPropositional (PFormula atom)

-- | Interpretation of formulas.
eval :: JustPropositional pf => pf -> (AtomOf pf -> Bool) -> Bool
eval fm v =
    foldPropositional co ne tf at fm
    where
      co p (:&:) q = (eval p v) && (eval q v)
      co p (:|:) q = (eval p v) || (eval q v)
      co p (:=>:) q = not (eval p v) || (eval q v)
      co p (:<=>:) q = (eval p v) == (eval q v)
      ne p = not (eval p v)
      tf = id
      at = v

-- | Recognizing tautologies.
tautology :: JustPropositional pf => pf -> Bool
tautology fm = onallvaluations (&&) (eval fm) (\_s -> False) (atoms fm)

-- | Related concepts.
unsatisfiable :: JustPropositional pf => pf -> Bool
unsatisfiable = tautology . (.~.)
satisfiable :: JustPropositional pf  => pf -> Bool
satisfiable = not . unsatisfiable

onallvaluations :: Ord atom => (r -> r -> r) -> ((atom -> Bool) -> r) -> (atom -> Bool) -> Set atom -> r
onallvaluations cmb subfn v ats =
    case minView ats of
      Nothing -> subfn v
      Just (p, ps) ->
          let v' t q = (if q == p then t else v q) in
          cmb (onallvaluations cmb subfn (v' False) ps) (onallvaluations cmb subfn (v' True) ps)

-- | Return the set of propositional variables in a formula.
atoms :: IsFormula formula => formula -> Set (AtomOf formula)
atoms fm = atom_union singleton fm

data TruthTable a = TruthTable [a] [TruthTableRow] deriving (Eq, Show)
type TruthTableRow = ([Bool], Bool)

-- | Code to print out truth tables.
truthTable :: JustPropositional pf => pf -> TruthTable (AtomOf pf)
truthTable fm =
    TruthTable atl (onallvaluations (<>) mkRow (const False) ats)
    where
      ats = atoms fm
      mkRow v = [(List.map v atl, eval fm v)]
      atl = Set.toAscList ats

instance Pretty atom => Pretty (TruthTable atom) where
    pPrint (TruthTable ats rows) = vcat (List.map (text . intercalate "|" . center) rows'')
        where
          center :: [String] -> [String]
          center cols = Prelude.map (uncurry center') (zip colWidths cols)
          center' :: Int -> String -> String
          center' width s = let (q, r) = divMod (width - length s) 2 in replicate q ' ' ++ s ++ replicate (q + r) ' '
          hdrs = List.map prettyShow ats ++ ["result"]
          rows'' = hdrs : List.map (uncurry replicate) (zip colWidths (repeat '-')) : rows'
          rows' :: [[String]]
          rows' = List.map (\(cols, result) -> List.map prettyShow (cols ++ [result])) rows
          cellWidths :: [[Int]]
          cellWidths = List.map (List.map length) (hdrs : rows')
          colWidths :: [Int]
          colWidths = List.map (foldl1 max) (transpose cellWidths)

transpose               :: [[a]] -> [[a]]
transpose []             = []
transpose ([]   : xss)   = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [ t | (_:t) <- xss])

-- | Make sure the precedence and associativity implied by the Haskell
-- infix/infixl/infixr declarations matches the precedence and
-- associativity implied by the HasFixity instances.  It would be nice
-- to define one in terms of the other, but I don't know how to query
-- the precedence and associativity of an operator, and I don't know
-- how to (successfully) generate an infix/infixl/infixr declaration
-- using template haskell (the obvious thing didn't work:
--
--    $(pure [InfixD (Fixity quantPrec TH.InfixR) '(∀)])

-- | Tests precedence handling in pretty
-- printer.  1. Need to test: associativity of like operators
-- 2. precedence of every pair of adjacent operators 3. Stuff about
-- infix operators
test00 :: Test
test00 =
{-
    TestList [testPrecedence, testAssociativity]
    where
      testPrecedence :: Test
      testPrecedence =
          TestList (
-}
    TestList (List.map (\(input, expected) -> TestCase $ assertEqual "precedence" (text expected) (pPrint input))
                      [( p .&. (q .|. r)   , "p∧(q∨r)" ),
                       ( (p .&. q) .|. r   , "(p∧q)∨r" ),
                       ( p .&. q .|. r     , "(p∧q)∨r" ),
                       ( p .|. q .&. r     , "p∨(q∧r)" ),
                       ( p .&. q .&. r     , "p∧q∧r"   ),
                       ( p .|. q .|. r     , "p∨q∨r"   ),
                       ( (p .=>. q) .=>. r , "(p⇒q)⇒r" ),
                       ( p .=>. (q .=>. r) , "p⇒q⇒r"   ),
                       ( p .=>. q .=>. r   , "p⇒q⇒r"   )])
    where
      byPrec :: IsPropositional formula => [[(Rational, formula -> formula -> formula)]]
      byPrec = groupBy ((==) `on` fst) . sortBy (compare `on` fst) $ binops
      -- All the operators we will test, with the 'Precedence' value
      -- we assigned.  we need to make sure the 'Precedence' value
      -- matches the values in the infix/infixl/infixr declarations.
      binops :: IsPropositional formula => [(Rational, formula -> formula -> formula)]
      binops = ands ++ ors ++ imps ++ iffs
          where
            ands :: IsPropositional formula => [(Rational, formula -> formula -> formula)]
            ands = List.map (andPrec,) [(.&.), (∧), (·)]
            ors :: IsPropositional formula => [(Rational, formula -> formula -> formula)]
            ors = List.map (orPrec,) [(.|.), (∨)]
            imps :: IsPropositional formula => [(Rational, formula -> formula -> formula)]
            imps = List.map (impPrec,) [(.=>.), (⇒), (==>), (→), (⊃)]
            iffs :: IsPropositional formula => [(Rational, formula -> formula -> formula)]
            iffs = List.map (iffPrec,) [(.<=>.), (<=>), (⇔), (↔)]
      preops :: IsPropositional formula => [(Rational, formula -> formula)]
      preops = nots
          where
            nots :: IsPropositional formula => [(Rational, formula -> formula)]
            nots = List.map (notPrec,) [(.~.), (¬)]
      (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))
      -- What about these?
      -- (∴)


{-
test00 = TestCase $ assertEqual "parenthesization" expected (List.map prettyShow input)
          (input, expected) = unzip [( p .&. (q .|. r)   , "p∧(q∨r)" ),
                                     ( (p .&. q) .|. r   , "(p∧q)∨r" ),
                                     ( p .&. q .|. r     , "(p∧q)∨r" ),
                                     ( p .|. q .&. r     , "p∨(q∧r)" ),
                                     ( p .&. q .&. r     , "p∧q∧r"   ),
                                     ( (p .=>. q) .=>. r , "(p⇒q)⇒r" ),
                                     ( p .=>. (q .=>. r) , "p⇒q⇒r"   ),
                                     ( p .=>. q .=>. r   , "p⇒q⇒r"   )]
-}

test01 :: Test
test01 =
    let fm = atomic "p" .=>. atomic "q" .<=>. (atomic "r" .&. atomic "s") .|. (atomic "t" .<=>. ((.~.) ((.~.) (atomic "u"))) .&. atomic "v") :: PFormula Prop
        input = (prettyShow fm, show fm)
        expected = (-- Pretty printed
                    "p⇒q⇔(r∧s)∨(t⇔u∧v)",
                    -- Haskell expression
                    "atomic \"p\" .=>. atomic \"q\" .<=>. (atomic \"r\" .&. atomic \"s\") .|. (atomic \"t\" .<=>. atomic \"u\" .&. atomic \"v\")"
                    ) in
    TestCase $ assertEqual "Build Formula 1" expected input

test02 :: Test
test02 = TestCase $ assertEqual "Build Formula 2" expected input
    where input = (Atom "fm" .&. Atom "fm") :: PFormula Prop
          expected = (And (Atom "fm") (Atom "fm"))

test03 :: Test
test03 = TestCase $ assertEqual "Build Formula 3"
                                (Atom "fm" .|. Atom "fm" .&. Atom "fm" :: PFormula Prop)
                                (Or (Atom "fm") (And (Atom "fm") (Atom "fm")))

-- Example of use.

test04 :: Test
test04 = TestCase $ assertEqual "fixity tests" expected input
    where (input, expected) = unzip (List.map (\ (fm, flag) -> (eval fm v0, flag)) pairs)
          v0 x = error $ "v0: " ++ show x
          pairs :: [(PFormula Prop, Bool)]
          pairs =
              [ ( true .&. false .=>. false .&. true,  True)
              , ( true .&. true  .=>. true  .&. false, False)
              , (   false ∧  true  ∨ true,             True)  -- "∧ binds more tightly than ∨"
              , (  (false ∧  true) ∨ true,             True)
              , (   false ∧ (true  ∨ true),            False)
              , (  (¬) true ∨ true,                    True)  -- "¬ binds more tightly than ∨"
              , (  (¬) (true ∨ true),                  False)
              ]

-- Example.

test06 :: Test
test06 = TestCase $ assertEqual "atoms test" (atoms $ p .&. q .|. s .=>. ((.~.) p) .|. (r .<=>. s)) (Set.fromList [P "p",P "q",P "r",P "s"])
    where (p, q, r, s) = (Atom (P "p"), Atom (P "q"), Atom (P "r"), Atom (P "s"))

-- Example.

test07 :: Test
test07 = TestCase $ assertEqual "truth table 1 (p. 36)" expected input
    where input = (truthTable $ p .&. q .=>. q .&. r)
          expected =
              (TruthTable
               [P "p", P "q", P "r"]
               [([False,False,False],True),
               ([False,False,True],True),
               ([False,True,False],True),
               ([False,True,True],True),
               ([True,False,False],True),
               ([True,False,True],True),
               ([True,True,False],False),
               ([True,True,True],True)])
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- Additional examples illustrating formula classes.

test08 :: Test
test08 = TestCase $
    assertEqual "truth table 2 (p. 39)"
                (truthTable $  ((p .=>. q) .=>. p) .=>. p)
                (TruthTable
                 [P "p", P "q"]
                 [([False,False],True),
                  ([False,True],True),
                  ([True,False],True),
                  ([True,True],True)])
        where (p, q) = (Atom (P "p"), Atom (P "q"))

test09 :: Test
test09 = TestCase $
    assertEqual "truth table 3 (p. 40)" expected input
        where input = (truthTable $ p .&. ((.~.) p))
              expected = (TruthTable
                          [P "p"]
                          [([False],False),
                          ([True],False)])
              p = Atom (P "p")

-- Examples.

test10 :: Test
test10 = TestCase $ assertEqual "tautology 1 (p. 41)" True (tautology $ p .|. ((.~.) p)) where p = Atom (P "p")
test11 :: Test
test11 = TestCase $ assertEqual "tautology 2 (p. 41)" False (tautology $ p .|. q .=>. p) where (p, q) = (Atom (P "p"), Atom (P "q"))
test12 :: Test
test12 = TestCase $ assertEqual "tautology 3 (p. 41)" False (tautology $ p .|. q .=>. q .|. (p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))
test13 :: Test
test13 = TestCase $ assertEqual "tautology 4 (p. 41)" True (tautology $ (p .|. q) .&. ((.~.)(p .&. q)) .=>. ((.~.)p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))

-- | Substitution operation.
psubst :: JustPropositional formula => Map (AtomOf formula) formula -> formula -> formula
psubst subfn fm =
    foldPropositional co ne tf at fm
    where
      co p op q = binop (psubst subfn p) op (psubst subfn q)
      ne p = (.~.) (psubst subfn p)
      tf = fromBool
      at p = fromMaybe (atomic p) (fpf subfn p)

-- Example
test14 :: Test
test14 =
    TestCase $ assertEqual "pSubst (p. 41)" expected input
        where expected = (p .&. q) .&. q .&. (p .&. q) .&. q
              input = psubst ((P "p") |=> (p .&. q)) (p .&. q .&. p .&. q)
              (p, q) = (Atom (P "p"), Atom (P "q"))

-- Surprising tautologies including Dijkstra's "Golden rule".

test15 :: Test
test15 = TestCase $ assertEqual "tautology 5 (p. 43)" expected input
    where input = tautology $ (p .=>. q) .|. (q .=>. p)
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test16 :: Test
test16 = TestCase $ assertEqual "tautology 6 (p. 45)" expected input
    where input = tautology $ p .|. (q .<=>. r) .<=>. (p .|. q .<=>. p .|. r)
          expected = True
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))
test17 :: Test
test17 = TestCase $ assertEqual "Dijkstra's Golden Rule (p. 45)" expected input
    where input = tautology $ p .&. q .<=>. ((p .<=>. q) .<=>. p .|. q)
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test18 :: Test
test18 = TestCase $ assertEqual "Contraposition 1 (p. 46)" expected input
    where input = tautology $ (p .=>. q) .<=>. (((.~.)q) .=>. ((.~.)p))
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test19 :: Test
test19 = TestCase $ assertEqual "Contraposition 2 (p. 46)" expected input
    where input = tautology $ (p .=>. ((.~.)q)) .<=>. (q .=>. ((.~.)p))
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test20 :: Test
test20 = TestCase $ assertEqual "Contraposition 3 (p. 46)" expected input
    where input = tautology $ (p .=>. q) .<=>. (q .=>. p)
          expected = False
          (p, q) = (Atom (P "p"), Atom (P "q"))

-- Some logical equivalences allowing elimination of connectives.

test21 :: Test
test21 = TestCase $ assertEqual "Equivalences (p. 47)" expected input
    where input =
              List.map tautology
              [ true .<=>. false .=>. false
              , ((.~.)p) .<=>. p .=>. false
              , p .&. q .<=>. (p .=>. q .=>. false) .=>. false
              , p .|. q .<=>. (p .=>. false) .=>. q
              , (p .<=>. q) .<=>. ((p .=>. q) .=>. (q .=>. p) .=>. false) .=>. false ]
          expected = [True, True, True, True, True]
          (p, q) = (Atom (P "p"), Atom (P "q"))

-- | Dualization.
dual :: JustPropositional pf => pf -> pf
dual fm =
    foldPropositional co ne tf (\_ -> fm) fm
    where
      tf True = false
      tf False = true
      ne p = (.~.) (dual p)
      co p (:&:) q = dual p .|. dual q
      co p (:|:) q = dual p .&. dual q
      co _ _ _ = error "Formula involves connectives .=>. or .<=>."

-- Example.
test22 :: Test
test22 = TestCase $ assertEqual "Dual (p. 49)" expected input
    where input = dual (Atom (P "p") .|. ((.~.) (Atom (P "p"))))
          expected = And (Atom (P {pname = "p"})) (Not (Atom (P {pname = "p"})))

-- | Routine simplification.
psimplify :: IsPropositional formula => formula -> formula
psimplify fm =
    foldPropositional' ho co ne tf at fm
    where
      ho _ = fm
      ne p = psimplify1 ((.~.) (psimplify p))
      co p (:&:) q = psimplify1 ((psimplify p) .&. (psimplify q))
      co p (:|:) q = psimplify1 ((psimplify p) .|. (psimplify q))
      co p (:=>:) q = psimplify1 ((psimplify p) .=>. (psimplify q))
      co p (:<=>:) q = psimplify1 ((psimplify p) .<=>. (psimplify q))
      tf _ = fm
      at _ = fm

psimplify1 :: IsPropositional formula => formula -> formula
psimplify1 fm =
    foldPropositional' (\_ -> fm) simplifyCombine simplifyNegate (\_ -> fm) (\_ -> fm) fm
    where
      simplifyNegate p = foldPropositional' (\_ -> fm) simplifyNotCombine simplifyNotNegate (fromBool . not) simplifyNotAtom p
      simplifyCombine l op r =
          case (asBool l, op , asBool r) of
            (Just True,  (:&:), _)            -> r
            (Just False, (:&:), _)            -> fromBool False
            (_,          (:&:), Just True)    -> l
            (_,          (:&:), Just False)   -> fromBool False
            (Just True,  (:|:), _)            -> fromBool True
            (Just False, (:|:), _)            -> r
            (_,          (:|:), Just True)    -> fromBool True
            (_,          (:|:), Just False)   -> l
            (Just True,  (:=>:), _)           -> r
            (Just False, (:=>:), _)           -> fromBool True
            (_,          (:=>:), Just True)   -> fromBool True
            (_,          (:=>:), Just False)  -> (.~.) l
            (Just False, (:<=>:), Just False) -> fromBool True
            (Just True,  (:<=>:), _)          -> r
            (Just False, (:<=>:), _)          -> (.~.) r
            (_,          (:<=>:), Just True)  -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _                                 -> fm
      simplifyNotNegate f = f
      simplifyNotCombine _ _ _ = fm
      simplifyNotAtom x = (.~.) (atomic x)

-- Example.
test23 :: Test
test23 = TestCase $ assertEqual "psimplify 1 (p. 50)" expected input
    where input = psimplify $ (true .=>. (x .<=>. false)) .=>. ((.~.) (y .|. false .&. z))
          expected = ((.~.) x) .=>. ((.~.) y)
          x = Atom (P "x")
          y = Atom (P "y")
          z = Atom (P "z")

test24 :: Test
test24 = TestCase $ assertEqual "psimplify 2 (p. 51)" expected input
    where input = psimplify $ ((x .=>. y) .=>. true) .|. (.~.) false
          expected = true
          x = Atom (P "x")
          y = Atom (P "y")

-- | Negation normal form.

nnf :: JustPropositional pf => pf -> pf
nnf = nnf1 . psimplify

nnf1 :: JustPropositional pf => pf -> pf
nnf1 fm = foldPropositional nnfCombine nnfNegate fromBool (\_ -> fm) fm
    where
      -- nnfCombine :: (IsPropositional formula atom) => formula -> Combination formula -> formula
      nnfNegate p = foldPropositional nnfNotCombine nnfNotNegate (fromBool . not) (\_ -> fm) p
      nnfCombine p (:=>:) q = nnf1 ((.~.) p) .|. (nnf1 q)
      nnfCombine p (:<=>:) q =  (nnf1 p .&. nnf1 q) .|. (nnf1 ((.~.) p) .&. nnf1 ((.~.) q))
      nnfCombine p (:&:) q = nnf1 p .&. nnf1 q
      nnfCombine p (:|:) q = nnf1 p .|. nnf1 q

      -- nnfNotCombine :: (IsPropositional formula atom) => Combination formula -> formula
      nnfNotNegate p = nnf1 p
      nnfNotCombine p (:&:) q = nnf1 ((.~.) p) .|. nnf1 ((.~.) q)
      nnfNotCombine p (:|:) q = nnf1 ((.~.) p) .&. nnf1 ((.~.) q)
      nnfNotCombine p (:=>:) q = nnf1 p .&. nnf1 ((.~.) q)
      nnfNotCombine p (:<=>:) q = (nnf1 p .&. nnf1 ((.~.) q)) .|. nnf1 ((.~.) p) .&. nnf1 q

-- Example of NNF function in action.

test25 :: Test
test25 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = nnf $ (p .<=>. q) .<=>. ((.~.)(r .=>. s))
          expected = Or (And (Or (And p q) (And (Not p) (Not q)))
                        (And r (Not s)))
                        (And (Or (And p (Not q)) (And (Not p) q))
                             (Or (Not r) s))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
          s = Atom (P "s")

test26 :: Test
test26 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = tautology (Iff fm fm')
          expected = True
          fm' = nnf fm
          fm = (p .<=>. q) .<=>. ((.~.)(r .=>. s))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
          s = Atom (P "s")

nenf :: IsPropositional formula => formula -> formula
nenf = nenf' . psimplify

-- | Simple negation-pushing when we don't care to distinguish occurrences.
nenf' :: IsPropositional formula => formula -> formula
nenf' fm =
    foldPropositional' (\_ -> fm) co ne (\_ -> fm) (\_ -> fm) fm
    where
      ne p = foldPropositional' (\_ -> fm) co' ne' (\_ -> fm) (\_ -> fm) p
      co p (:&:) q = nenf' p .&. nenf' q
      co p (:|:) q = nenf' p .|. nenf' q
      co p (:=>:) q = nenf' ((.~.) p) .|. nenf' q
      co p (:<=>:) q = nenf' p .<=>. nenf' q
      ne' p = p
      co' p (:&:) q = nenf' ((.~.) p) .|. nenf' ((.~.) q)
      co' p (:|:) q = nenf' ((.~.) p) .&. nenf' ((.~.) q)
      co' p (:=>:) q = nenf' p .&. nenf' ((.~.) q)
      co' p (:<=>:) q = nenf' p .<=>. nenf' ((.~.) q) -- really?  how is this asymmetrical?

-- Some tautologies remarked on.

test27 :: Test
test27 = TestCase $ assertEqual "tautology 1 (p. 53)" expected input
    where input = tautology $ (p .=>. p') .&. (q .=>. q') .=>. (p .&. q .=>. p' .&. q')
          expected = True
          p = Atom (P "p")
          q = Atom (P "q")
          p' = Atom (P "p'")
          q' = Atom (P "q'")
test28 :: Test
test28 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = tautology $ (p .=>. p') .&. (q .=>. q') .=>. (p .|. q .=>. p' .|. q')
          expected = True
          p = Atom (P "p")
          q = Atom (P "q")
          p' = Atom (P "p'")
          q' = Atom (P "q'")

dnfSet :: (JustPropositional pf, Ord pf) => pf -> pf
dnfSet fm =
    list_disj (List.map (mk_lits (Set.map atomic pvs)) satvals)
    where
      satvals = allsatvaluations (eval fm) (\_s -> False) pvs
      pvs = atoms fm

mk_lits :: (JustPropositional pf, Ord pf) => Set pf -> (AtomOf pf -> Bool) -> pf
mk_lits pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

allsatvaluations :: Ord atom => ((atom -> Bool) -> Bool) -> (atom -> Bool) -> Set atom -> [atom -> Bool]
allsatvaluations subfn v pvs =
    case Set.minView pvs of
      Nothing -> if subfn v then [v] else []
      Just (p, ps) -> (allsatvaluations subfn (\a -> if a == p then False else v a) ps) ++
                      (allsatvaluations subfn (\a -> if a == p then True else v a) ps)

-- | Disjunctive normal form (DNF) via truth tables.
list_conj :: (Foldable t, IsFormula formula, IsPropositional formula) => t formula -> formula
list_conj l | null l = true
list_conj l = foldl1 (.&.) l

list_disj :: (Foldable t, IsFormula formula, IsPropositional formula) => t formula -> formula
list_disj l | null l = false
list_disj l = foldl1 (.|.) l

-- This is only used in the test below, its easier to match lists than sets.
dnfList :: JustPropositional pf => pf -> pf
dnfList fm =
    list_disj (List.map (mk_lits' (List.map atomic (Set.toAscList pvs))) satvals)
     where
       satvals = allsatvaluations (eval fm) (\_s -> False) pvs
       pvs = atoms fm
       mk_lits' :: JustPropositional pf => [pf] -> (AtomOf pf -> Bool) -> pf
       mk_lits' pvs' v = list_conj (List.map (\ p -> if eval p v then p else (.~.) p) pvs')

-- Examples.

test29 :: Test
test29 = TestCase $ assertEqual "dnf 1 (p. 56)" expected input
    where input = (dnfList fm, truthTable fm)
          expected = ((((((.~.) p) .&. q) .&. r) .|. ((p .&. ((.~.) q)) .&. ((.~.) r))) .|. ((p .&. q) .&. ((.~.) r)),
                      TruthTable
                      [P "p", P "q", P "r"]
                      [([False,False,False],False),
                       ([False,False,True],False),
                       ([False,True,False],False),
                       ([False,True,True],True),
                       ([True,False,False],True),
                       ([True,False,True],False),
                       ([True,True,False],True),
                       ([True,True,True],False)])
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

test30 :: Test
test30 = TestCase $ assertEqual "dnf 2 (p. 56)" expected input
    where input = dnfList (p .&. q .&. r .&. s .&. t .&. u .|. u .&. v :: PFormula Prop)
          expected = (((((((((((((((((((((((((((((((((((((((.~.) p) .&. ((.~.) q)) .&. ((.~.) r)) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v) .|.
                                                    ((((((((.~.) p) .&. ((.~.) q)) .&. ((.~.) r)) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                                                   ((((((((.~.) p) .&. ((.~.) q)) .&. ((.~.) r)) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                                  ((((((((.~.) p) .&. ((.~.) q)) .&. ((.~.) r)) .&. s) .&. t) .&. u) .&. v)) .|.
                                                 ((((((((.~.) p) .&. ((.~.) q)) .&. r) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                                ((((((((.~.) p) .&. ((.~.) q)) .&. r) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                                               ((((((((.~.) p) .&. ((.~.) q)) .&. r) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                              ((((((((.~.) p) .&. ((.~.) q)) .&. r) .&. s) .&. t) .&. u) .&. v)) .|.
                                             ((((((((.~.) p) .&. q) .&. ((.~.) r)) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                            ((((((((.~.) p) .&. q) .&. ((.~.) r)) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                                           ((((((((.~.) p) .&. q) .&. ((.~.) r)) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                          ((((((((.~.) p) .&. q) .&. ((.~.) r)) .&. s) .&. t) .&. u) .&. v)) .|.
                                         ((((((((.~.) p) .&. q) .&. r) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                        ((((((((.~.) p) .&. q) .&. r) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                                       ((((((((.~.) p) .&. q) .&. r) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                      ((((((((.~.) p) .&. q) .&. r) .&. s) .&. t) .&. u) .&. v)) .|.
                                     ((((((p .&. ((.~.) q)) .&. ((.~.) r)) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                    ((((((p .&. ((.~.) q)) .&. ((.~.) r)) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                                   ((((((p .&. ((.~.) q)) .&. ((.~.) r)) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                  ((((((p .&. ((.~.) q)) .&. ((.~.) r)) .&. s) .&. t) .&. u) .&. v)) .|.
                                 ((((((p .&. ((.~.) q)) .&. r) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                                ((((((p .&. ((.~.) q)) .&. r) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                               ((((((p .&. ((.~.) q)) .&. r) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                              ((((((p .&. ((.~.) q)) .&. r) .&. s) .&. t) .&. u) .&. v)) .|.
                             ((((((p .&. q) .&. ((.~.) r)) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                            ((((((p .&. q) .&. ((.~.) r)) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                           ((((((p .&. q) .&. ((.~.) r)) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                          ((((((p .&. q) .&. ((.~.) r)) .&. s) .&. t) .&. u) .&. v)) .|.
                         ((((((p .&. q) .&. r) .&. ((.~.) s)) .&. ((.~.) t)) .&. u) .&. v)) .|.
                        ((((((p .&. q) .&. r) .&. ((.~.) s)) .&. t) .&. u) .&. v)) .|.
                       ((((((p .&. q) .&. r) .&. s) .&. ((.~.) t)) .&. u) .&. v)) .|.
                      ((((((p .&. q) .&. r) .&. s) .&. t) .&. u) .&. ((.~.) v))) .|.
                     ((((((p .&. q) .&. r) .&. s) .&. t) .&. u) .&. v)
          [p, q, r, s, t, u, v] = List.map (Atom . P) ["p", "q", "r", "s", "t", "u", "v"]

-- | DNF via distribution.
distrib1 :: IsPropositional formula => formula -> formula
distrib1 fm =
    foldCombination (\_ -> fm) (\_ _ -> fm) lhs (\_ _ -> fm) (\_ _ -> fm) fm
    where
      -- p & (q | r) -> (p & q) | (p & r)
      lhs p qr = foldCombination (\_ -> rhs p qr)
                                 (\q r -> distrib1 (p .&. q) .|. distrib1 (p .&. r))
                                 (\_ _ -> rhs p qr)
                                 (\_ _ -> rhs p qr)
                                 (\_ _ -> rhs p qr)
                                 qr
      -- (p | q) & r -> (p & r) | (q & r)
      rhs pq r = foldCombination (\_ -> fm)
                                 (\p q -> distrib1 (p .&. r) .|. distrib1 (q .&. r))
                                 (\_ _ -> fm)
                                 (\_ _ -> fm)
                                 (\_ _ -> fm)
                                 pq
{-
distrib1 :: Formula atom -> Formula atom
distrib1 fm =
  case fm of
    And p (Or q r) -> Or (distrib1 (And p q)) (distrib1 (And p r))
    And (Or p q) r -> Or (distrib1 (And p r)) (distrib1 (And q r))
    _ -> fm
-}

rawdnf :: IsPropositional formula => formula -> formula
rawdnf fm =
    foldPropositional' (\_ -> fm) co (\_ -> fm) (\_ -> fm) (\_ -> fm) fm
    where
      co p (:&:) q = distrib1 (rawdnf p .&. rawdnf q)
      co p (:|:) q = (rawdnf p .|. rawdnf q)
      co _ _ _ = fm
{-
rawdnf :: Ord atom => Formula atom -> Formula atom
rawdnf fm =
  case fm of
    And p q -> distrib1 (And (rawdnf p) (rawdnf q))
    Or p q -> Or (rawdnf p) (rawdnf q)
    _ -> fm
-}

-- Example.

test31 :: Test
test31 = TestCase $ assertEqual "rawdnf (p. 58)" (prettyShow expected) (prettyShow input)
    where input :: PFormula Prop
          input = rawdnf $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected :: PFormula Prop
          expected = ((atomic (P "p")) .&. ((.~.)(atomic (P "p"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "p")))) .|.
                     ((atomic (P "p")) .&. ((.~.)(atomic (P "r"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "r"))))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

purednf :: (JustPropositional pf,
            IsLiteral lit, JustLiteral lit, Ord lit) => (AtomOf pf -> AtomOf lit) -> pf -> Set (Set lit)
purednf ca fm =
    foldPropositional co (\_ -> l2f fm) (\_ -> l2f fm) (\_ -> l2f fm) fm
    where
      l2f f = singleton . singleton . convertToLiteral (error $ "purednf failure: " ++ prettyShow f) ca $ f
      co p (:&:) q = distrib (purednf ca p) (purednf ca q)
      co p (:|:) q = union (purednf ca p) (purednf ca q)
      co _ _ _ = l2f fm

-- Example.

test32 :: Test
test32 = TestCase $ assertEqual "purednf (p. 58)" expected (purednf id fm)
    where fm :: PFormula Prop
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected :: Set (Set (LFormula Prop))
          expected = Set.map (Set.map (convertToLiteral (error "test32") id)) $
                     Set.fromList [Set.fromList [p, (.~.) p],
                                   Set.fromList [p, (.~.) r],
                                   Set.fromList [q, r, (.~.) p],
                                   Set.fromList [q, r, (.~.) r]]
          p = atomic (P "p")
          q = atomic (P "q")
          r = atomic (P "r")

-- | Filtering out trivial disjuncts (in this guise, contradictory).
trivial :: (Ord lit, IsLiteral lit) => Set lit -> Bool
trivial lits =
    let (pos, neg) = Set.partition positive lits in
    (not . null . Set.intersection neg . Set.map (.~.)) pos

-- Example.
test33 :: Test
test33 = TestCase $ assertEqual "trivial" expected (Set.filter (not . trivial) (purednf id fm))
    where expected :: Set (Set (LFormula Prop))
          expected = Set.map (Set.map (convertToLiteral (error "test32") id)) $
                     Set.fromList [Set.fromList [p,(.~.) r],
                                   Set.fromList [q,r,(.~.) p]]
          fm :: PFormula Prop
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = atomic (P "p") :: PFormula Prop
          q = atomic (P "q") :: PFormula Prop
          r = atomic (P "r") :: PFormula Prop

-- | With subsumption checking, done very naively (quadratic).
simpdnf :: (JustPropositional pf,
            IsLiteral lit, JustLiteral lit, Ord lit
           ) => (AtomOf pf -> AtomOf lit) -> pf -> Set (Set lit)
simpdnf ca fm =
    foldPropositional (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf ca (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs

-- | Mapping back to a formula.
dnf :: forall pf. (JustPropositional pf, Ord pf) => pf -> pf
dnf fm = (list_disj . Set.toAscList . Set.map list_conj .
          Set.map (Set.map (convertLiteral id :: LFormula (AtomOf pf) -> pf)) . simpdnf id) fm

-- Example. (p. 56)
test34 :: Test
test34 = TestCase $ assertEqual "dnf (p. 56)" expected input
    where input = (prettyShow (dnf fm), tautology (Iff fm (dnf fm)))
          expected = ("(p∧¬r)∨(q∧r∧¬p)",True)
          fm = let (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r")) in
               (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))

-- | Conjunctive normal form (CNF) by essentially the same code. (p. 60)
purecnf :: (JustPropositional pf, JustLiteral lit, Ord lit) =>
           (AtomOf pf -> AtomOf lit) -> pf -> Set (Set lit)
purecnf ca fm = Set.map (Set.map negate) (purednf ca (nnf ((.~.) fm)))

simpcnf :: (JustPropositional pf, JustLiteral lit, Ord lit) =>
           (AtomOf pf -> AtomOf lit) -> pf -> Set (Set lit)
simpcnf ca fm =
    foldPropositional (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let cjs = Set.filter (not . trivial) (purecnf ca fm) in
           Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

cnf_ :: (IsPropositional pf, Ord pf, JustLiteral lit) => (AtomOf lit -> AtomOf pf) -> Set (Set lit) -> pf
cnf_ ca = list_conj . Set.map (list_disj . Set.map (convertLiteral ca))

cnf' :: forall pf. (JustPropositional pf, Ord pf) => pf -> pf
cnf' fm = (list_conj . Set.map list_disj . Set.map (Set.map (convertLiteral id :: LFormula (AtomOf pf) -> pf)) . simpcnf id) fm

-- Example. (p. 61)
test35 :: Test
test35 = TestCase $ assertEqual "cnf (p. 61)" expected input
    where input = (prettyShow (cnf' fm), tautology (Iff fm (cnf' fm)))
          expected = ("(p∨q)∧(p∨r)∧(¬p∨¬r)", True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          [p, q, r] = [Atom (P "p"), Atom (P "q"), Atom (P "r")]

testProp :: Test
testProp = TestLabel "Prop" $
           TestList [test00, test01, test02, test03, test04, {-test05,-}
                     test06, test07, test08, test09, test10,
                     test11, test12, test13, test14, test15,
                     test16, test17, test18, test19, test20,
                     test21, test22, test23, test24, test25,
                     test26, test27, test28, test29, test30,
                     test31, test32, test33, test34, test35]
