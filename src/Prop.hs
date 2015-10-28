-- | Basic stuff for propositional logic: datatype, parsing and
-- printing.  'IsPropositional' is a subclass of 'IsLiteral' of
-- formula types that support binary combinations.

{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Prop
    ( IsAtom
    , IsPropositional( foldPropositional')
    , foldPropositional
    , convertPropositional
    , convertToPropositional
    , zipPropositional
    , fixityPropositional
    , prettyPropositional
    , showPropositional
    -- * Formula marker types and restricted formula classes
    , Literal
    , Propositional
    , markLiteral
    , unmarkLiteral
    , JustLiteral
    , JustPropositional
    , markPropositional
    , unmarkPropositional
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
    , cnf', cnf_
    , trivial
#ifndef NOTESTS
    -- * Instance
    , Prop(P, pname)
    , PFormula(F, T, Atom, Not, And, Or, Imp, Iff)
    -- * Tests
    , testProp
#endif
    ) where

import Data.Foldable as Foldable (null)
import Data.Generics (Data, Typeable)
import Data.List as List (map, intercalate)
import Data.Map as Map (Map)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, intersection, isProperSubsetOf, map,
                        minView, partition, Set, singleton, toAscList, union)
import Formulas (atom_union, binop,
                 HasBoolean(fromBool, asBool), true, false,
                 IsNegatable(naiveNegate, foldNegation'), (.~.), negate, positive,
                 IsCombinable((.&.), (.|.), (.=>.), (.<=>.), foldCombination),
                 BinOp((:&:), (:|:), (:=>:), (:<=>:)),
                 IsFormula(atomic, overatoms, onatoms))
import Lib (distrib, fpf, Marked(..), setAny)
import Lit (convertLiteral, convertToLiteral, IsLiteral(foldLiteral'), JustLiteral)
import Prelude hiding (negate, null)
import Pretty (Associativity(InfixN, InfixR, InfixA), Doc, Expr, Fixity(Fixity), HasFixity(fixity),
              markExpr, parenthesize, Pretty(pPrint), prettyShow, rootFixity, Side(LHS, RHS, Unary), text)
import Text.PrettyPrint.HughesPJClass (braces, parens, vcat)
#ifndef NOTESTS
import Data.Set as Set (fromList)
import Data.String (IsString(fromString))
import Formulas ((¬), (∧), (∨))
import Lib ((|=>))
import Lit (LFormula)
import Pretty (leafFixity)
import Test.HUnit (Test(TestCase, TestLabel, TestList), assertEqual)
#endif

-- | Basic properties of an atomic formula
class (Ord atom, Show atom, HasFixity atom, Pretty atom) => IsAtom atom

-- |A type class for propositional logic.  If the type we are writing
-- an instance for is a zero-order (aka propositional) logic type
-- there will generally by a type or a type parameter corresponding to
-- atom.  For first order or predicate logic types, it is generally
-- easiest to just use the formula type itself as the atom type, and
-- raise errors in the implementation if a non-atomic formula somehow
-- appears where an atomic formula is expected (i.e. as an argument to
-- atomic or to the third argument of foldPropositional.)
class (IsLiteral formula atom, IsCombinable formula) => IsPropositional formula atom where
    -- | Build an atomic formula from the atom type.
    -- | A fold function that distributes different sorts of formula
    -- to its parameter functions, one to handle binary operators, one
    -- for negations, and one for atomic formulas.  See examples of its
    -- use to implement the polymorphic functions below.
    foldPropositional' :: (formula -> r)
                       -> (formula -> BinOp -> formula -> r)
                       -> (formula -> r)
                       -> (Bool -> r)
                       -> (atom -> r)
                       -> formula -> r

foldPropositional :: (IsPropositional pf atom, JustPropositional pf) =>
                     (pf -> BinOp -> pf -> r)
                  -> (pf -> r)
                  -> (Bool -> r)
                  -> (atom -> r)
                  -> pf -> r
foldPropositional = foldPropositional' (error "JustPropositional failure")

-- | Combine two formulas if they are similar.
zipPropositional :: (IsPropositional pf1 atom1, JustPropositional pf1,
                     IsPropositional pf2 atom2, JustPropositional pf2) =>
                    (pf1 -> BinOp -> pf1 -> pf2 -> BinOp -> pf2 -> Maybe r)
                 -> (pf1 -> pf2 -> Maybe r)
                 -> (Bool -> Bool -> Maybe r)
                 -> (atom1 -> atom2 -> Maybe r)
                 -> pf1 -> pf2 -> Maybe r
zipPropositional co ne tf at fm1 fm2 =
    foldPropositional co' ne' tf' at' fm1
    where
      co' l1 op1 r1 = foldPropositional (co l1 op1 r1) (\_ -> Nothing) (\_ -> Nothing) (\_ -> Nothing) fm2
      ne' x1 = foldPropositional (\_ _ _ -> Nothing)     (ne x1)     (\_ -> Nothing) (\_ -> Nothing) fm2
      tf' x1 = foldPropositional (\_ _ _ -> Nothing) (\_ -> Nothing)     (tf x1)     (\_ -> Nothing) fm2
      at' a1 = foldPropositional (\_ _ _ -> Nothing) (\_ -> Nothing) (\_ -> Nothing)     (at a1)     fm2

-- | Convert any instance of JustPropositional to any IsPropositional formula.
convertPropositional :: (IsPropositional pf1 a1, JustPropositional pf1, IsPropositional pf2 a2) => (a1 -> a2) -> pf1 -> pf2
convertPropositional ca pf =
    foldPropositional co ne tf (atomic . ca) pf
    where
      co p (:&:) q = (convertPropositional ca p) .&. (convertPropositional ca q)
      co p (:|:) q = (convertPropositional ca p) .|. (convertPropositional ca q)
      co p (:=>:) q = (convertPropositional ca p) .=>. (convertPropositional ca q)
      co p (:<=>:) q = (convertPropositional ca p) .<=>. (convertPropositional ca q)
      ne p = (.~.) (convertPropositional ca p)
      tf = fromBool

-- | Convert any instance of IsPropositional to a JustPropositional formula.
convertToPropositional :: (IsPropositional formula atom1, IsPropositional pf atom2, JustPropositional pf) =>
                          (formula -> pf) -> (atom1 -> atom2) -> formula -> pf
convertToPropositional ho ca fm =
    foldPropositional' ho co ne tf (atomic . ca) fm
    where
      co p (:&:) q = (convertToPropositional ho ca p) .&. (convertToPropositional ho ca q)
      co p (:|:) q = (convertToPropositional ho ca p) .|. (convertToPropositional ho ca q)
      co p (:=>:) q = (convertToPropositional ho ca p) .=>. (convertToPropositional ho ca q)
      co p (:<=>:) q = (convertToPropositional ho ca p) .<=>. (convertToPropositional ho ca q)
      ne p = (.~.) (convertToPropositional ho ca p)
      tf = fromBool

fixityPropositional :: (IsPropositional pf atom, JustPropositional pf) => pf -> Fixity
fixityPropositional fm =
    foldPropositional co ne tf at fm
    where
      ne _ = Fixity 5 InfixN
      co _ (:&:) _ = Fixity 4 InfixA
      co _ (:|:) _ = Fixity 3 InfixA
      co _ (:=>:) _ = Fixity 2 InfixR
      co _ (:<=>:) _ = Fixity 1 InfixA
      tf _ = Fixity 10 InfixN
      at = fixity

prettyPropositional :: (IsPropositional pf atom, JustPropositional pf) => pf -> Doc
prettyPropositional fm0 =
    go rootFixity Unary fm0
    where
      go parentFixity side fm =
          parenthesize parens braces parentFixity fix side $ foldPropositional co ne tf at fm
          where
            fix = fixity fm
            co f (:&:) g = go fix LHS f <> text "∧" <> go fix RHS g
            co f (:|:) g = go fix LHS f <> text "∨" <> go fix RHS g
            co f (:=>:) g = go fix LHS f <> text "⇒" <> go fix RHS g
            co f (:<=>:) g = go fix LHS f <> text "⇔" <> go fix RHS g
            ne f = text "¬" <> go fix Unary f
            tf = pPrint
            at a = pPrint a

-- | For clarity, show methods fully parenthesize
showPropositional :: (IsPropositional pf atom, JustPropositional pf, Show atom) => pf -> String
showPropositional fm0 =
    go rootFixity Unary fm0
    where
      go parentFixity side fm =
          parenthesize' (\s -> "(" <> s <> ")") (\s -> "{" <> s <> "}") parentFixity fix side $ foldPropositional co ne tf at fm
          where
            fix = fixity fm
            ne f = "(.~.) (" <> go fix Unary f ++ ")" -- parenthesization of prefix operators is sketchy
            co f (:&:) g = go fix LHS f <> " .&. " <> go fix RHS g
            co f (:|:) g = go fix LHS f <> " .|. " <> go fix RHS g
            co f (:=>:) g = go fix LHS f <> " .=>. " <> go fix RHS g
            co f (:<=>:) g = go fix LHS f <> " .<=>. " <> go fix RHS g
            tf = show
            at = show
      parenthesize' parens braces _ _ _ fm = parenthesize parens braces leafFixity rootFixity Unary fm

onatomsPropositional :: (IsPropositional pf atom, JustPropositional pf) => (atom -> pf) -> pf -> pf
onatomsPropositional f fm =
    foldPropositional co ne tf at fm
    where
      co p op q = binop (onatomsPropositional f p) op (onatomsPropositional f q)
      ne p = (.~.) (onatomsPropositional f p)
      tf flag = fromBool flag
      at x = f x

overatomsPropositional :: (IsPropositional pf atom, JustPropositional pf) => (atom -> r -> r) -> pf -> r -> r
overatomsPropositional f fof r0 =
    foldPropositional co ne (const r0) (flip f r0) fof
    where
      co p _ q = overatomsPropositional f p (overatomsPropositional f q r0)
      ne fof' = overatomsPropositional f fof' r0

---------------------------------------------------------
-- Formula marker types and restricted formula classes --
---------------------------------------------------------

instance HasFixity formula => HasFixity (Marked mk formula) where
    fixity (Mark x) = fixity x

instance IsFormula formula atom => IsFormula (Marked mk formula) atom where
    atomic = Mark . atomic
    overatoms at (Mark fm) = overatoms at fm
    onatoms at (Mark fm) = Mark (onatoms (unMark' . at) fm)

instance HasBoolean formula => HasBoolean (Marked mk formula) where
    asBool (Mark x) = asBool x
    fromBool x = Mark (fromBool x)

instance IsNegatable formula => IsNegatable (Marked mk formula) where
    naiveNegate (Mark x) = Mark (naiveNegate x)
    foldNegation' ne ot (Mark x) = foldNegation' (ne . Mark) (ot . Mark) x

instance (IsLiteral formula atom, IsNegatable formula) => IsLiteral (Marked mk formula) atom where
    foldLiteral' ho ne tf at (Mark x) = foldLiteral' (ho . Mark) (ne . Mark) tf at x

instance IsCombinable formula => IsCombinable (Marked mk formula) where
    (Mark a) .|. (Mark b) = Mark (a .|. b)
    (Mark a) .&. (Mark b) = Mark (a .&. b)
    (Mark a) .=>. (Mark b) = Mark (a .=>. b)
    (Mark a) .<=>. (Mark b) = Mark (a .<=>. b)
    foldCombination dj cj imp iff other fm =
        foldCombination (\a b -> dj a b)
                        (\a b -> cj a b)
                        (\a b -> imp a b)
                        (\a b -> iff a b)
                        (\a -> other a)
                        fm

instance Pretty formula => Pretty (Marked mk formula) where
    pPrint = pPrint . unMark'

instance IsPropositional formula atom => IsPropositional (Marked mk formula) atom where
    foldPropositional' ho co ne tf at (Mark x) = foldPropositional' (ho . Mark) co' (ne . Mark) tf at x
        where
          co' lhs op rhs = co (Mark lhs) op (Mark rhs)

-- | The formula marker types
data Literal
data Propositional
deriving instance Data Literal
deriving instance Data Propositional

-- We only want these simple instances for specific markings, not the
-- general Marked mk case.
instance Show formula => Show (Marked Literal formula) where
    show (Mark x) = "markLiteral (" ++ show x ++ ")"

instance Eq formula => Eq (Marked Literal formula) where
    Mark a == Mark b = a == b

instance Show formula => Show (Marked Propositional formula) where
    show (Mark x) = "markPropositional (" ++ show x ++ ")"

instance Eq formula => Eq (Marked Propositional formula) where
    Mark a == Mark b = a == b

instance Ord formula => Ord (Marked Literal formula)where
    compare (Mark a) (Mark b) = compare a b

instance Ord formula => Ord (Marked Propositional formula)where
    compare (Mark a) (Mark b) = compare a b

instance Show (Marked Expr formula) => Show (Marked Expr (Marked Literal formula)) where
    show (Mark (Mark fm)) = "markLiteral (" ++ show (markExpr fm) ++ ")"

instance Show (Marked Expr formula) => Show (Marked Expr (Marked Propositional formula)) where
    show (Mark (Mark fm)) = "markPropositional (" ++ show (markExpr fm) ++ ")"

-- | Class that indicates a formula type *only* supports Propositional
-- features - no quantifiers.
class JustPropositional formula

instance JustLiteral (Marked Literal formula)
instance JustPropositional (Marked Propositional formula)
instance JustPropositional (Marked Literal formula)

markLiteral :: IsLiteral lit atom => lit -> Marked Literal lit
markLiteral = Mark

unmarkLiteral :: IsLiteral pf atom => Marked Literal pf -> pf
unmarkLiteral = unMark'

markPropositional :: IsPropositional lit atom => lit -> Marked Propositional lit
markPropositional fm = convertToPropositional (error "markPropositional") id fm

unmarkPropositional :: IsPropositional pf atom => Marked Propositional pf -> pf
unmarkPropositional fm = convertPropositional id fm

#ifndef NOTESTS
instance JustPropositional (PFormula atom)
instance JustPropositional (LFormula atom)

data Prop = P {pname :: String} deriving (Eq, Ord, Show)

instance IsAtom Prop

-- Allows us to say "q" instead of P "q" or P {pname = "q"}
instance IsString Prop where
    fromString = P

instance HasBoolean Prop where
    asBool (P "True") = Just True
    asBool (P "False") = Just False
    asBool _ = Nothing
    fromBool = P . show

-- Because of the IsString instance, the Show instance can just
-- be a String.
instance Show (Marked Expr Prop) where
    show (Mark (P {pname = s})) = show s

instance Pretty Prop where
    pPrint = text . pname

instance HasFixity Prop where
    fixity _ = leafFixity

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

instance HasBoolean (PFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance Ord atom => IsNegatable (PFormula atom) where
    naiveNegate = Not
    foldNegation' inverted normal (Not x) = foldNegation' normal inverted x
    foldNegation' _ normal x = normal x

instance Ord atom => IsCombinable (PFormula atom) where
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

-- infixr 9 !, ?, ∀, ∃

-- Display formulas using infix notation
instance Show (Marked Expr atom) => Show (Marked Expr (PFormula atom)) where
    show (Mark F) = "false"
    show (Mark T) = "true"
    show (Mark (Atom atom)) = "atomic (" ++ show (markExpr atom) ++ ")"
    show (Mark (Not f)) = "(.~.) (" ++ show (markExpr f) ++ ")"
    show (Mark (And f g)) = "(" ++ show (markExpr f) ++ ") .&. (" ++ show (markExpr g) ++ ")"
    show (Mark (Or f g)) = "(" ++ show (markExpr f) ++ ") .|. (" ++ show (markExpr g) ++ ")"
    show (Mark (Imp f g)) = "(" ++ show (markExpr f) ++ ") .=>. (" ++ show (markExpr g) ++ ")"
    show (Mark (Iff f g)) = "(" ++ show (markExpr f) ++ ") .<=>. (" ++ show (markExpr g) ++ ")"

-- Build a Haskell expression for this formula
instance (IsPropositional (PFormula atom) atom, Show atom) => Show (PFormula atom) where
    show = showPropositional

instance IsAtom atom => HasFixity (PFormula atom) where
    fixity = fixityPropositional

instance IsAtom atom => IsFormula (PFormula atom) atom where
    atomic = Atom
    overatoms = overatomsPropositional
    onatoms = onatomsPropositional

instance IsAtom atom => IsPropositional (PFormula atom) atom where
    foldPropositional' _ co ne tf at fm =
        case fm of
          Imp p q -> co p (:=>:) q
          Iff p q -> co p (:<=>:) q
          And p q -> co p (:&:) q
          Or p q -> co p (:|:) q
          _ -> foldLiteral' (error "IsPropositional PFormula") ne tf at fm

instance IsAtom atom => IsLiteral (PFormula atom) atom where
    foldLiteral' ho ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not l -> ne l
          _ -> ho fm

instance IsAtom atom => Pretty (PFormula atom) where
    pPrint = prettyPropositional
#endif

data TruthTable a = TruthTable [a] [TruthTableRow] deriving (Eq, Show)
type TruthTableRow = ([Bool], Bool)

-- | Code to print out truth tables.
truthTable :: (IsPropositional pf atom, JustPropositional pf, Ord atom) => pf -> TruthTable atom
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

#ifndef NOTESTS
-- | Tests precedence handling in pretty printer.
test00 :: Test
test00 = TestCase $ assertEqual "parenthesization" expected (List.map prettyShow input)
    where (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))
          (input, expected) = unzip [( p .&. (q .|. r)   , "p∧(q∨r)" ),
                                     ( (p .&. q) .|. r   , "(p∧q)∨r" ),
                                     ( p .&. q .|. r     , "(p∧q)∨r" ),
                                     ( p .|. q .&. r     , "p∨(q∧r)" ),
                                     ( p .&. q .&. r     , "p∧q∧r"   ),
                                     ( (p .=>. q) .=>. r , "(p⇒q)⇒r" ),
                                     ( p .=>. (q .=>. r) , "p⇒q⇒r"   ),
                                     ( p .=>. q .=>. r   , "p⇒q⇒r"   )]

-- Testing the parser and printer.

test01 :: Test
test01 =
    let fm = atomic "p" .=>. atomic "q" .<=>. atomic "r" .&. atomic "s" .|. (atomic "t" .<=>. ((.~.) ((.~.) (atomic "u"))) .&. atomic "v") :: PFormula Prop
        input = (prettyShow fm, show (markExpr fm))
        expected = (-- Pretty printed
                    "p⇒q⇔(r∧s)∨(t⇔u∧v)",
                    -- Haskell expression
                    "((atomic (\"p\")) .=>. (atomic (\"q\"))) .<=>. (((atomic (\"r\")) .&. (atomic (\"s\"))) .|. ((atomic (\"t\")) .<=>. ((atomic (\"u\")) .&. (atomic (\"v\")))))") in
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

instance HasBoolean String where
    asBool "True" = Just True
    asBool "False" = Just False
    asBool _ = Nothing
    fromBool = show

instance IsAtom String

test04 :: Test
test04 = TestCase $ assertEqual "fixity tests" expected input
    where (input, expected) = unzip (List.map (\ (fm, flag) -> (eval fm v0, flag)) pairs)
          v0 x = error $ "v0: " ++ show x
          pairs :: [(PFormula String, Bool)]
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
#endif

-- | Recognizing tautologies.
tautology :: (IsPropositional pf atom, JustPropositional pf, Ord atom) => pf -> Bool
tautology fm = onallvaluations (&&) (eval fm) (\_s -> False) (atoms fm)

-- | Interpretation of formulas.
eval :: (IsPropositional pf atom, JustPropositional pf) => pf -> (atom -> Bool) -> Bool
eval fm v =
    foldPropositional co ne tf at fm
    where
      tf = id
      ne p = not (eval p v)
      co p (:&:) q = (eval p v) && (eval q v)
      co p (:|:) q = (eval p v) || (eval q v)
      co p (:=>:) q = not (eval p v) || (eval q v)
      co p (:<=>:) q = (eval p v) == (eval q v)
      at = v

onallvaluations :: Ord atom => (r -> r -> r) -> ((atom -> Bool) -> r) -> (atom -> Bool) -> Set atom -> r
onallvaluations cmb subfn v ats =
    case minView ats of
      Nothing -> subfn v
      Just (p, ps) ->
          let v' t q = (if q == p then t else v q) in
          cmb (onallvaluations cmb subfn (v' False) ps) (onallvaluations cmb subfn (v' True) ps)

-- | Return the set of propositional variables in a formula.
atoms :: IsFormula formula atom => formula -> Set atom
atoms fm = atom_union singleton fm

#ifndef NOTESTS
-- Examples.

test10 :: Test
test10 = TestCase $ assertEqual "tautology 1 (p. 41)" True (tautology $ p .|. ((.~.) p)) where p = Atom (P "p")
test11 :: Test
test11 = TestCase $ assertEqual "tautology 2 (p. 41)" False (tautology $ p .|. q .=>. p) where (p, q) = (Atom (P "p"), Atom (P "q"))
test12 :: Test
test12 = TestCase $ assertEqual "tautology 3 (p. 41)" False (tautology $ p .|. q .=>. q .|. (p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))
test13 :: Test
test13 = TestCase $ assertEqual "tautology 4 (p. 41)" True (tautology $ (p .|. q) .&. ((.~.)(p .&. q)) .=>. ((.~.)p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))
#endif

-- | Related concepts.
unsatisfiable :: (IsPropositional pf atom, JustPropositional pf) => pf -> Bool
unsatisfiable = tautology . (.~.)
satisfiable :: (IsPropositional pf atom, JustPropositional pf)  => pf -> Bool
satisfiable = not . unsatisfiable

-- | Substitution operation.
psubst :: IsPropositional formula atom => Map atom formula -> formula -> formula
psubst subfn fm = onatoms (\ p -> maybe (atomic p) id (fpf subfn p)) fm

#ifndef NOTESTS
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
#endif

-- | Dualization.
dual :: (IsPropositional pf atom, JustPropositional pf) => pf -> pf
dual fm =
    foldPropositional co ne tf (\_ -> fm) fm
    where
      tf True = false
      tf False = true
      ne p = (.~.) (dual p)
      co p (:&:) q = dual p .|. dual q
      co p (:|:) q = dual p .&. dual q
      co _ _ _ = error "Formula involves connectives .=>. or .<=>."

#ifndef NOTESTS
-- Example.
test22 :: Test
test22 = TestCase $ assertEqual "Dual (p. 49)" expected input
    where input = dual (Atom (P "p") .|. ((.~.) (Atom (P "p"))))
          expected = And (Atom (P {pname = "p"})) (Not (Atom (P {pname = "p"})))
#endif

-- | Routine simplification.
psimplify :: IsPropositional formula atom => formula -> formula
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

psimplify1 :: IsPropositional formula atom => formula -> formula
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

#ifndef NOTESTS
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
#endif

-- | Negation normal form.

nnf :: (IsPropositional pf atom, JustPropositional pf) => pf -> pf
nnf = nnf1 . psimplify

nnf1 :: (IsPropositional pf atom, JustPropositional pf) => pf -> pf
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

#ifndef NOTESTS
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
#endif

nenf :: IsPropositional formula atom => formula -> formula
nenf = nenf' . psimplify

-- | Simple negation-pushing when we don't care to distinguish occurrences.
nenf' :: IsPropositional formula atom => formula -> formula
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

#ifndef NOTESTS
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
#endif

dnfSet :: (IsPropositional pf atom, JustPropositional pf, Ord pf) => pf -> pf
dnfSet fm =
    list_disj (List.map (mk_lits (Set.map atomic pvs)) satvals)
    where
      satvals = allsatvaluations (eval fm) (\_s -> False) pvs
      pvs = atoms fm

mk_lits :: (IsPropositional pf atom, JustPropositional pf, Ord pf) => Set pf -> (atom -> Bool) -> pf
mk_lits pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

allsatvaluations :: Ord atom => ((atom -> Bool) -> Bool) -> (atom -> Bool) -> Set atom -> [atom -> Bool]
allsatvaluations subfn v pvs =
    case Set.minView pvs of
      Nothing -> if subfn v then [v] else []
      Just (p, ps) -> (allsatvaluations subfn (\a -> if a == p then False else v a) ps) ++
                      (allsatvaluations subfn (\a -> if a == p then True else v a) ps)

-- | Disjunctive normal form (DNF) via truth tables.
list_conj :: (Foldable t, HasBoolean formula, IsCombinable formula) => t formula -> formula
list_conj l | null l = true
list_conj l = foldl1 (.&.) l

list_disj :: (Foldable t, HasBoolean formula, IsCombinable formula) => t formula -> formula
list_disj l | null l = false
list_disj l = foldl1 (.|.) l

#ifndef NOTESTS
-- This is only used in the test below, its easier to match lists than sets.
dnfList :: (IsPropositional pf atom, JustPropositional pf) => pf -> pf
dnfList fm =
    list_disj (List.map (mk_lits' (List.map atomic (Set.toAscList pvs))) satvals)
     where
       satvals = allsatvaluations (eval fm) (\_s -> False) pvs
       pvs = atoms fm
       mk_lits' :: (IsPropositional pf atom, JustPropositional pf) => [pf] -> (atom -> Bool) -> pf
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
#endif

-- | DNF via distribution.
distrib1 :: IsPropositional formula atom => formula -> formula
distrib1 fm =
    foldCombination (\_ _ -> fm) lhs (\_ _ -> fm) (\_ _ -> fm) (\_ -> fm) fm
    where
      -- p & (q | r) -> (p & q) | (p & r)
      lhs p qr = foldCombination (\q r -> distrib1 (p .&. q) .|. distrib1 (p .&. r))
                                 (\_ _ -> rhs p qr)
                                 (\_ _ -> rhs p qr)
                                 (\_ _ -> rhs p qr)
                                 (\_ -> rhs p qr)
                                 qr
      -- (p | q) & r -> (p & r) | (q & r)
      rhs pq r = foldCombination (\p q -> distrib1 (p .&. r) .|. distrib1 (q .&. r))
                                 (\_ _ -> fm)
                                 (\_ _ -> fm)
                                 (\_ _ -> fm)
                                 (\_ -> fm)
                                 pq
{-
distrib1 :: Formula atom -> Formula atom
distrib1 fm =
  case fm of
    And p (Or q r) -> Or (distrib1 (And p q)) (distrib1 (And p r))
    And (Or p q) r -> Or (distrib1 (And p r)) (distrib1 (And q r))
    _ -> fm
-}

rawdnf :: IsPropositional formula atom => formula -> formula
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
#ifndef NOTESTS
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
#endif

purednf :: (IsPropositional pf atom, JustPropositional pf,
            IsLiteral lit atom2, JustLiteral lit, Ord lit) => (atom -> atom2) -> pf -> Set (Set lit)
purednf ca fm =
    foldPropositional co (\_ -> l2f fm) (\_ -> l2f fm) (\_ -> l2f fm) fm
    where
      l2f f = singleton . singleton . convertToLiteral (error $ "purednf failure: " ++ prettyShow f) ca $ f
      co p (:&:) q = distrib (purednf ca p) (purednf ca q)
      co p (:|:) q = union (purednf ca p) (purednf ca q)
      co _ _ _ = l2f fm

#ifndef NOTESTS
-- Example.

test32 :: Test
test32 = TestCase $ assertEqual "purednf (p. 58)" expected input
    where input = purednf id $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected :: Set (Set (Marked Literal (PFormula Prop)))
          expected = Set.fromList [Set.fromList [p, (.~.) p],
                                   Set.fromList [p, (.~.) r],
                                   Set.fromList [q, r, (.~.) p],
                                   Set.fromList [q, r, (.~.) r]]
          p = atomic (P "p")
          q = atomic (P "q")
          r = atomic (P "r")
#endif

-- | Filtering out trivial disjuncts (in this guise, contradictory).
trivial :: (Ord lit, IsNegatable lit) => Set lit -> Bool
trivial lits =
    let (pos, neg) = Set.partition positive lits in
    (not . null . Set.intersection neg . Set.map (.~.)) pos

#ifndef NOTESTS
-- Example.
test33 :: Test
test33 = TestCase $ assertEqual "trivial" expected input
    where input = Set.filter (not . trivial) (purednf id fm)
          expected :: Set (Set (Marked Literal (PFormula Prop)))
          expected = Set.fromList [Set.fromList [p,(.~.) r],
                                   Set.fromList [q,r,(.~.) p]]
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = atomic (P "p")
          q = atomic (P "q")
          r = atomic (P "r")
#endif

-- | With subsumption checking, done very naively (quadratic).
simpdnf :: (IsPropositional pf atom, JustPropositional pf,
            IsLiteral lit atom2, JustLiteral lit, Ord lit
           ) => (atom -> atom2) -> pf -> Set (Set lit)
simpdnf ca fm =
    foldPropositional (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf ca (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs

-- | Mapping back to a formula.
dnf :: (IsPropositional pf atom, JustPropositional pf, Eq pf, Ord pf) => pf -> pf
dnf fm = (list_disj . Set.toAscList . Set.map list_conj . Set.map (Set.map unmarkLiteral) . simpdnf id) fm

#ifndef NOTESTS
-- Example. (p. 56)
test34 :: Test
test34 = TestCase $ assertEqual "dnf (p. 56)" expected input
    where input = (prettyShow (dnf fm), tautology (Iff fm (dnf fm)))
          expected = ("(p∧¬r)∨(q∧r∧¬p)",True)
          fm = let (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r")) in
               (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
#endif

-- | Conjunctive normal form (CNF) by essentially the same code. (p. 60)
purecnf :: (IsPropositional pf atom, JustPropositional pf,
            IsLiteral lit atom2, JustLiteral lit, Ord lit) => (atom -> atom2) -> pf -> Set (Set lit)
purecnf ca fm = Set.map (Set.map negate) (purednf ca (nnf ((.~.) fm)))

simpcnf :: (IsPropositional pf atom, JustPropositional pf,
            IsLiteral lit atom2, JustLiteral lit, Ord lit) => (atom -> atom2) -> pf -> Set (Set lit)
simpcnf ca fm =
    foldPropositional (\_ _ _ -> go) (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let cjs = Set.filter (not . trivial) (purecnf ca fm) in
           Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

{-
instance (IsLiteral lit atom, JustLiteral lit) => IsPropositional (Set (Set lit)) where
    foldPropositional' ho co tf at fm =
        case Set.minView fm of
          Nothing -> tf False
          Just (s, ss) | Set.null s && Set.null ss -> tf True
          Just (s, ss) -> co
-}

cnf_ :: (IsPropositional pf atom, Ord pf, IsLiteral lit atom2, JustLiteral lit) => (atom2 -> atom) -> Set (Set lit) -> pf
cnf_ ca = list_conj . Set.map (list_disj . Set.map (convertLiteral ca))

cnf' :: (IsPropositional pf atom, JustPropositional pf, Ord pf) => pf -> pf
cnf' fm = (list_conj . Set.map list_disj . Set.map (Set.map unmarkLiteral) . simpcnf id) fm

#ifndef NOTESTS
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
#endif
