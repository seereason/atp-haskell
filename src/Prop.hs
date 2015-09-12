-- | Basic stuff for propositional logic: datatype, parsing and printing.
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Prop
    ( IsPropositional(foldPropositional)
    , convertPropositional
    , zipPropositional
    , propositionalFromLiteral
    , literalFromPropositional
    , prettyPropositional
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
    , dnfList
    , purednf
    , simpdnf
    , dnf
    , purecnf
    , simpcnf
    , cnf', cnf_
    , trivial
    -- * Instance
    , Prop(P, pname)
    , PFormula(F, T, Atom, Not, And, Or, Imp, Iff)
    -- * Tests
    , tests
    ) where

import Data.Foldable as Foldable (null)
import Data.List as List (map)
import Data.Map as Map (Map)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, fromList, intersection, isProperSubsetOf, map, minView, partition, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import Formulas (atom_union,
                 HasBoolean(fromBool, asBool), true, false,
                 IsNegatable(naiveNegate, foldNegation), (.~.), negate, positive,
                 IsCombinable((.&.), (.|.), (.=>.), (.<=>.)), (¬), (∧), (∨),
                 Combination((:~:), BinOp), BinOp((:&:), (:|:), (:=>:), (:<=>:)),
                 IsFormula(atomic, overatoms, onatoms), onatoms)
import Lib (fpf, (|=>), allpairs, setAny)
import Lit (IsLiteral(foldLiteral))
import Pretty (Fixity(Fixity), Associativity(InfixN, InfixR, InfixA), HasFixity(fixity),
              leafFixity, parenthesize, rootFixity, Side(LHS, RHS, Unary))
import Prelude hiding (negate, null)
import Test.HUnit (Test(TestCase, TestLabel, TestList), assertEqual)
import Text.PrettyPrint.HughesPJClass hiding ((<>))

-- |A type class for propositional logic.  If the type we are writing
-- an instance for is a zero-order (aka propositional) logic type
-- there will generally by a type or a type parameter corresponding to
-- atom.  For first order or predicate logic types, it is generally
-- easiest to just use the formula type itself as the atom type, and
-- raise errors in the implementation if a non-atomic formula somehow
-- appears where an atomic formula is expected (i.e. as an argument to
-- atomic or to the third argument of foldPropositional.)
class (IsFormula formula atom,
       IsLiteral formula atom,
       IsNegatable formula,
       IsCombinable formula,
       HasBoolean formula
      ) => IsPropositional formula atom where
    -- | Build an atomic formula from the atom type.
    -- | A fold function that distributes different sorts of formula
    -- to its parameter functions, one to handle binary operators, one
    -- for negations, and one for atomic formulas.  See examples of its
    -- use to implement the polymorphic functions below.
    foldPropositional :: (Combination formula -> r)
                      -> (Bool -> r)
                      -> (atom -> r)
                      -> formula -> r

-- | Combine two formulas if they are similar.
zipPropositional :: IsPropositional formula atom =>
                    (Combination formula -> Combination formula -> Maybe r)
                 -> (Bool -> Bool -> Maybe r)
                 -> (atom -> atom -> Maybe r)
                 -> formula -> formula -> Maybe r
zipPropositional co tf at fm1 fm2 =
    foldPropositional co' tf' at' fm1
    where
      co' c1 = foldPropositional (co c1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldPropositional (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' atom1 = foldPropositional (\ _ -> Nothing) (\ _ -> Nothing) (at atom1) fm2

-- | Use foldPropositional to convert any instance of
-- IsPropositional to any other by specifying the result type.
convertPropositional :: (IsPropositional f1 a1, IsPropositional f2 a2) => (a1 -> a2) -> f1 -> f2
convertPropositional ca f1 =
    foldPropositional co tf (atomic . ca) f1
    where
      co ((:~:) p) = (.~.) (convertPropositional ca p)
      co (BinOp p (:&:) q) = (convertPropositional ca p) .&. (convertPropositional ca q)
      co (BinOp p (:|:) q) = (convertPropositional ca p) .|. (convertPropositional ca q)
      co (BinOp p (:=>:) q) = (convertPropositional ca p) .=>. (convertPropositional ca q)
      co (BinOp p (:<=>:) q) = (convertPropositional ca p) .<=>. (convertPropositional ca q)
      tf = fromBool

propositionalFromLiteral :: (IsLiteral lit atom1, IsPropositional pf atom2) =>
                            (atom1 -> atom2) -> lit -> pf
propositionalFromLiteral ca lit =
    foldLiteral ne fromBool (atomic . ca) lit
    where
      ne p = (.~.) (propositionalFromLiteral ca p)

literalFromPropositional :: (IsPropositional pf atom1, IsLiteral lit atom2) =>
                            (atom1 -> atom2) -> pf -> lit
literalFromPropositional ca =
    foldPropositional co fromBool (atomic . ca)
    where
      co ((:~:) p) = (.~.) (literalFromPropositional ca p)
      co _ = error "literalFromPropositional found binary operator"

instance (Ord atom, Pretty atom, HasFixity atom, Show atom) => Pretty (PFormula atom) where
    pPrint fm = prettyPropositional rootFixity Unary fm

prettyPropositional :: (IsPropositional formula atom, Pretty atom, HasFixity formula, Show formula, Show atom) => Fixity -> Side -> formula -> Doc
prettyPropositional pfix side fm =
    parenthesize pfix fix side $ foldPropositional co tf at fm
    -- bool id parens (trace ("fix=" ++ show fix ++ ", pfix= " ++ show pfix ++ ", fm=" ++ show fm) (pfix > fix)) $ foldPropositional co tf at fm
    where
      fix = fixity fm
      co ((:~:) f) = text "¬" <> prettyPropositional fix Unary f
      co (BinOp f (:&:) g) = prettyPropositional fix LHS f <> text "∧" <> prettyPropositional fix RHS g
      co (BinOp f (:|:) g) = prettyPropositional fix LHS f <> text "∨" <> prettyPropositional fix RHS g
      co (BinOp f (:=>:) g) = prettyPropositional fix LHS f <> text "⇒" <> prettyPropositional fix RHS g
      co (BinOp f (:<=>:) g) = prettyPropositional fix LHS f <> text "⇔" <> prettyPropositional fix RHS g
      tf = pPrint
      at = pPrint

data Prop = P {pname :: String} deriving (Eq, Ord)

-- Allows us to say "q" instead of P "q" or P {pname = "q"}
instance IsString Prop where
    fromString = P

-- Because of the IsString instance, the Show instance can just
-- be a String.
instance Show Prop where
    show (P {pname = s}) = show s

instance Pretty Prop where
    pPrint (P s) = text s

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
    deriving (Eq, Ord, Read)

instance HasBoolean (PFormula atom) where
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
    fromBool True = T
    fromBool False = F

instance IsNegatable (PFormula atom) where
    naiveNegate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance IsCombinable (PFormula atom) where
    (.|.) = Or
    (.&.) = And
    (.=>.) = Imp
    (.<=>.) = Iff

-- infixr 9 !, ?, ∀, ∃

-- Display formulas using infix notation
instance Show atom => Show (PFormula atom) where
    show F = "false"
    show T = "true"
    show (Atom atom) = "atomic (" ++ show atom ++ ")"
    show (Not f) = "(.~.) (" ++ show f ++ ")"
    show (And f g) = "(" ++ show f ++ ") .&. (" ++ show g ++ ")"
    show (Or f g) = "(" ++ show f ++ ") .|. (" ++ show g ++ ")"
    show (Imp f g) = "(" ++ show f ++ ") .=>. (" ++ show g ++ ")"
    show (Iff f g) = "(" ++ show f ++ ") .<=>. (" ++ show g ++ ")"

instance HasFixity atom => HasFixity (PFormula atom) where
    fixity T = Fixity 0 InfixN
    fixity F = Fixity 0 InfixN
    fixity (Atom a) = fixity a
    fixity (Not _) = Fixity 5 InfixN
    fixity (And _ _) = Fixity 4 InfixA
    fixity (Or _ _) = Fixity 3 InfixA
    fixity (Imp _ _) = Fixity 2 InfixR
    fixity (Iff _ _) = Fixity 1 InfixA

instance IsFormula (PFormula atom) atom where
    atomic = Atom
    overatoms f fm b =
      case fm of
        Atom a -> f a b
        Not p -> overatoms f p b
        And p q -> overatoms f p (overatoms f q b)
        Or p q -> overatoms f p (overatoms f q b)
        Imp p q -> overatoms f p (overatoms f q b)
        Iff p q -> overatoms f p (overatoms f q b)
        _ -> b
    onatoms f fm =
      case fm of
        Atom a -> f a
        Not p -> Not (onatoms f p)
        And p q -> And (onatoms f p) (onatoms f q)
        Or p q -> Or (onatoms f p) (onatoms f q)
        Imp p q -> Imp (onatoms f p) (onatoms f q)
        Iff p q -> Iff (onatoms f p) (onatoms f q)
        _ -> fm

instance IsPropositional (PFormula atom) atom where
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

instance IsLiteral (PFormula atom) atom where
    foldLiteral ne tf at fm =
        case fm of
          T -> tf True
          F -> tf False
          Atom a -> at a
          Not l -> ne l
          And _ _ -> error "And in Literal"
          Or _ _ -> error "Or in Literal"
          Imp _ _ -> error "Imp in Literal"
          Iff _ _ -> error "IFF in Literal"

data TruthTable a = TruthTable [a] [TruthTableRow] deriving (Eq, Show)
type TruthTableRow = ([Bool], Bool)

test00 :: Test
test00 = TestCase $ assertEqual "parenthesization" expected input
    where (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))
          input = List.map prettyShow
                    [p .&. (q .|. r),
                     (p .&. q) .|. r,
                     p .&. q .|. r,
                     (p .=>. q) .=>. r,
                     p .=>. (q .=>. r),
                     p .=>. q .=>. r]
          expected = ["p∧(q∨r)",
                      "(p∧q)∨r",
                      "(p∧q)∨r",
                      "(p⇒q)⇒r",
                      "p⇒q⇒r",
                      "p⇒q⇒r"]

-- Testing the parser and printer.

test01 :: Test
test01 =
    let fm = atomic "p" .=>. atomic "q" .<=>. atomic "r" .&. atomic "s" .|. (atomic "t" .<=>. ((.~.) ((.~.) (atomic "u"))) .&. atomic "v") :: PFormula Prop
        input = (prettyShow fm, show fm)
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

-- | Code to print out truth tables.
truthTable :: (IsPropositional formula atom, Ord atom) => formula -> TruthTable atom
truthTable fm =
    TruthTable atl (onallvaluations (<>) mkRow (const False) ats)
    where
      ats = atoms fm
      mkRow v = [(List.map v atl, eval fm v)]
      atl = Set.toAscList ats

-- | Recognizing tautologies.
tautology :: (IsPropositional formula atom, Ord atom) => formula -> Bool
tautology fm = onallvaluations (&&) (eval fm) (\_s -> False) (atoms fm)

-- | Interpretation of formulas.
eval :: IsPropositional formula atom => formula -> (atom -> Bool) -> Bool
eval fm v =
    foldPropositional co tf at fm
    where
      tf = id
      co ((:~:) p) = not (eval p v)
      co (BinOp p (:&:) q) = (eval p v) && (eval q v)
      co (BinOp p (:|:) q) = (eval p v) || (eval q v)
      co (BinOp p (:=>:) q) = not (eval p v) || (eval q v)
      co (BinOp p (:<=>:) q) = (eval p v) == (eval q v)
      at = v

onallvaluations :: Ord atom => (r -> r -> r) -> ((atom -> Bool) -> r) -> (atom -> Bool) -> Set atom -> r
onallvaluations cmb subfn v ats =
    case minView ats of
      Nothing -> subfn v
      Just (p, ps) ->
          let v' t q = (if q == p then t else v q) in
          cmb (onallvaluations cmb subfn (v' False) ps) (onallvaluations cmb subfn (v' True) ps)

-- | Return the set of propositional variables in a formula.
atoms :: (IsFormula formula atom, Ord atom) => formula -> Set atom
atoms fm = atom_union singleton fm

-- Examples.

test10 :: Test
test10 = TestCase $ assertEqual "tautology 1 (p. 41)" True (tautology $ p .|. ((.~.) p)) where p = Atom (P "p")
test11 :: Test
test11 = TestCase $ assertEqual "tautology 2 (p. 41)" False (tautology $ p .|. q .=>. p) where (p, q) = (Atom (P "p"), Atom (P "q"))
test12 :: Test
test12 = TestCase $ assertEqual "tautology 3 (p. 41)" False (tautology $ p .|. q .=>. q .|. (p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))
test13 :: Test
test13 = TestCase $ assertEqual "tautology 4 (p. 41)" True (tautology $ (p .|. q) .&. ((.~.)(p .&. q)) .=>. ((.~.)p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))

-- | Related concepts.
unsatisfiable :: (IsPropositional formula atom, Ord atom) => formula -> Bool
unsatisfiable = tautology . (.~.)
satisfiable :: (IsPropositional formula atom, Ord atom)  => formula -> Bool
satisfiable = not . unsatisfiable

-- | Substitution operation.
psubst :: (IsPropositional formula atom, Ord atom) => Map atom formula -> formula -> formula
psubst subfn fm = onatoms (\ p -> maybe (atomic p) id (fpf subfn p)) fm

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
dual :: IsPropositional formula atom => formula -> formula
dual fm =
    foldPropositional co tf (\_ -> fm) fm
    where
      tf True = false
      tf False = true
      co ((:~:) p) = (.~.) (dual p)
      co (BinOp p (:&:) q) = dual p .|. dual q
      co (BinOp p (:|:) q) = dual p .&. dual q
      co _ = error "Formula involves connectives .=>. or .<=>."

-- Example.
test22 :: Test
test22 = TestCase $ assertEqual "Dual (p. 49)" expected input
    where input = dual (Atom (P "p") .|. ((.~.) (Atom (P "p"))))
          expected = And (Atom (P {pname = "p"})) (Not (Atom (P {pname = "p"})))

-- | Routine simplification.
psimplify :: IsPropositional formula atom => formula -> formula
psimplify fm =
    foldPropositional co tf at fm
    where
      co ((:~:) p) = psimplify1 ((.~.) (psimplify p))
      co (BinOp p (:&:) q) = psimplify1 ((psimplify p) .&. (psimplify q))
      co (BinOp p (:|:) q) = psimplify1 ((psimplify p) .|. (psimplify q))
      co (BinOp p (:=>:) q) = psimplify1 ((psimplify p) .=>. (psimplify q))
      co (BinOp p (:<=>:) q) = psimplify1 ((psimplify p) .<=>. (psimplify q))
      tf _ = fm
      at _ = fm

psimplify1 :: IsPropositional formula atom => formula -> formula
psimplify1 fm =
    foldPropositional simplifyCombine (\_ -> fm) (\_ -> fm) fm
    where
      simplifyCombine ((:~:) p) = foldPropositional simplifyNotCombine (fromBool . not) simplifyNotAtom p
      simplifyCombine (BinOp l op r) =
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
      simplifyNotCombine ((:~:) f) = f
      simplifyNotCombine _ = fm
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

nnf :: IsPropositional formula atom => formula -> formula
nnf fm = foldPropositional nnfCombine fromBool (\ _ -> fm) fm
    where
      -- nnfCombine :: (IsPropositional formula atom) => formula -> Combination formula -> formula
      nnfCombine ((:~:) p) = foldPropositional nnfNotCombine (fromBool . not) (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q

      -- nnfNotCombine :: (IsPropositional formula atom) => Combination formula -> formula
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

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

nenf :: IsPropositional formula atom => formula -> formula
nenf = nenf' . psimplify

-- | Simple negation-pushing when we don't care to distinguish occurrences.
nenf' :: IsPropositional formula atom => formula -> formula
nenf' fm =
    foldPropositional co (\ _ -> fm) (\ _ -> fm) fm
    where
      co ((:~:) p) = foldPropositional co' (\ _ -> fm) (\ _ -> fm) p
      co (BinOp p (:&:) q) = nenf' p .&. nenf' q
      co (BinOp p (:|:) q) = nenf' p .|. nenf' q
      co (BinOp p (:=>:) q) = nenf' ((.~.) p) .|. nenf' q
      co (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' q
      co' ((:~:) p) = p
      co' (BinOp p (:&:) q) = nenf' ((.~.) p) .|. nenf' ((.~.) q)
      co' (BinOp p (:|:) q) = nenf' ((.~.) p) .&. nenf' ((.~.) q)
      co' (BinOp p (:=>:) q) = nenf' p .&. nenf' ((.~.) q)
      co' (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' ((.~.) q) -- really?  how is this asymmetrical?

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

dnfList :: (IsPropositional formula atom, Ord atom) => formula -> formula
dnfList fm =
    list_disj (List.map (mk_lits (List.map atomic (Set.toAscList pvs))) satvals)
     where
       satvals = allsatvaluations (eval fm) (\_s -> False) pvs
       pvs = atoms fm

dnfSet :: (IsPropositional formula atom, Ord formula, Ord atom) => formula -> formula
dnfSet fm =
    list_disj (List.map (mk_lits' (Set.map atomic pvs)) satvals)
    where
      satvals = allsatvaluations (eval fm) (\_s -> False) pvs
      pvs = atoms fm

mk_lits :: IsPropositional formula atom => [formula] -> (atom -> Bool) -> formula
mk_lits pvs v = list_conj (List.map (\ p -> if eval p v then p else (.~.) p) pvs)

mk_lits' :: (IsPropositional formula atom, Ord formula) => Set formula -> (atom -> Bool) -> formula
mk_lits' pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

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
distrib1 :: IsPropositional formula atom => formula -> formula
distrib1 fm =
    foldPropositional co (\_ -> fm) (\_ -> fm) fm
    where
      co (BinOp p (:&:) r) = foldPropositional (co' p r) (\_ -> fm) (\_ -> fm) r
      co _ = fm
      co' p _ (BinOp q (:|:) r) = distrib1 (p .&. q) .|. distrib1 (p .&. r) -- And p (Or q r)
      co' pq r _ = foldPropositional (co'' r) (\_ -> fm) (\_ -> fm) pq
      co'' r (BinOp p (:|:) q) = distrib1 (p .&. r) .|. distrib1 (q .&. r) -- And (Or p q) r
      co'' _ _ = fm
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
    foldPropositional co (\_ -> fm) (\_ -> fm) fm
    where
      co (BinOp p (:&:) q) = distrib1 (rawdnf p .&. rawdnf q)
      co (BinOp p (:|:) q) = (rawdnf p .|. rawdnf q)
      co _ = fm
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
test31 = TestCase $ assertEqual "rawdnf (p. 58)" expected input
    where input = rawdnf $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = ((atomic (P "p")) .&. ((.~.)(atomic (P "p"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "p")))) .|.
                     ((atomic (P "p")) .&. ((.~.)(atomic (P "r"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "r"))))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- | A version using a set of sets representation.
distrib2 :: Ord a => Set (Set a) -> Set (Set a) -> Set (Set a)
distrib2 s1 s2 = allpairs union s1 s2

purednf :: (IsPropositional formula atom, IsLiteral lit atom2, Ord lit) => (atom -> atom2) -> formula -> Set (Set lit)
purednf ca fm =
    foldPropositional co (\_ -> l2f fm) (\_ -> l2f fm) fm
    where
      l2f = singleton . singleton . literalFromPropositional ca
      co (BinOp p (:&:) q) = distrib2 (purednf ca p) (purednf ca q)
      co (BinOp p (:|:) q) = union (purednf ca p) (purednf ca q)
      co _ = l2f fm

-- Example.

test32 :: Test
test32 = TestCase $ assertEqual "purednf (p. 58)" expected input
    where input = purednf id $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = Set.fromList [Set.fromList [p,Not p],
                                   Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p],
                                   Set.fromList [q,r,Not r]]
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- | Filtering out trivial disjuncts (in this guise, contradictory).
trivial :: (Ord lit, IsNegatable lit) => Set lit -> Bool
trivial lits =
    not . null $ Set.intersection neg (Set.map (.~.) pos)
    where (pos, neg) = Set.partition positive lits

-- Example.
test33 :: Test
test33 = TestCase $ assertEqual "trivial" expected input
    where input = Set.filter (not . trivial) (purednf id fm)
          expected = Set.fromList [Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p]]
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- | With subsumption checking, done very naively (quadratic).
simpdnf :: (IsPropositional formula atom, IsLiteral lit atom2, Ord lit) => (atom -> atom2) -> formula -> Set (Set lit)
simpdnf ca fm =
    foldPropositional (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let djs = Set.filter (not . trivial) (purednf ca (nnf fm)) in
           Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs

-- | Mapping back to a formula.
dnf :: (IsPropositional formula atom, Ord formula) => formula -> formula
dnf fm = list_disj (Set.toAscList (Set.map list_conj (simpdnf id fm)))

-- Example. (p. 56)
test34 :: Test
test34 = TestCase $ assertEqual "dnf (p. 56)" expected input
    where input = (prettyShow (dnf fm), tautology (Iff fm (dnf fm)))
          expected = ("(p∧¬r)∨(q∧r∧¬p)",True)
          fm = let (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r")) in
               (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))

-- | Conjunctive normal form (CNF) by essentially the same code. (p. 60)
purecnf :: (IsPropositional formula atom, IsLiteral lit atom2, Ord lit) => (atom -> atom2) -> formula -> Set (Set lit)
purecnf ca fm = Set.map (Set.map negate) (purednf ca (nnf ((.~.) fm)))

simpcnf :: (IsPropositional formula atom, IsLiteral lit atom2, Ord lit) => (atom -> atom2) -> formula -> Set (Set lit)
simpcnf ca fm =
    foldPropositional (\_ -> go) tf (\_ -> go) fm
    where
      tf False = Set.empty
      tf True = singleton Set.empty
      go = let cjs = Set.filter (not . trivial) (purecnf ca fm) in
           Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

cnf_ :: forall pf atom lit atom2. (IsPropositional pf atom, Ord pf, IsLiteral lit atom2, Ord lit) => (atom2 -> atom) -> Set.Set (Set.Set lit) -> pf
cnf_ ca = list_conj . Set.map (list_disj . Set.map (propositionalFromLiteral ca))

cnf' :: (IsPropositional formula atom, Ord formula) => formula -> formula
cnf' fm = list_conj (Set.map list_disj (simpcnf id fm))

-- Example. (p. 61)
test35 :: Test
test35 = TestCase $ assertEqual "cnf (p. 61)" expected input
    where input = (prettyShow (cnf' fm), tautology (Iff fm (cnf' fm)))
          expected = ("(p∨q)∧(p∨r)∧(¬p∨¬r)", True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          [p, q, r] = [Atom (P "p"), Atom (P "q"), Atom (P "r")]

tests :: Test
tests = TestLabel "Prop" $ TestList [test00, test01, test02, test03, test04, {-test05,-}
                                     test06, test07, test08, test09, test10,
                                     test11, test12, test13, test14, test15,
                                     test16, test17, test18, test19, test20,
                                     test21, test22, test23, test24, test25,
                                     test26, test27, test28, test29, test30,
                                     test31, test32, test33, test34, test35]
