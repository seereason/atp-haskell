{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Prop
    ( Prop(P, pname)
    , TruthTable(TruthTable)
    , eval
    , atoms
    , onallvaluations
    , truthTable
    , tautology
    , unsatisfiable
    , satisfiable
    , psubst
    , dual
    , psimplify
    , psimplify1
    , negative, positive, negate
    , nnf
    , nenf
    , list_conj
    , list_disj
    , mk_lits
    , allsatvaluations
    , dnf1
    , purednf
    , dnf2
    , purecnf
    , simpcnf
    , cnf
    , trivial
    , tests
    ) where

import Data.List as List (map)
import Data.Map as Map (Map)
import Data.Monoid ((<>))
import Data.Set as Set (empty, filter, fold, fromList, intersection, isProperSubsetOf, map, minView, null, partition, Set, singleton, toAscList, union)
import Data.String (IsString(fromString))
import Formulas
import Lib (fpf, (|=>), allpairs, setAny)
import Prelude hiding (negate)
import Test.HUnit (Test(TestCase, TestLabel, TestList), assertEqual)

data Prop = P {pname :: String} deriving (Eq, Ord)

instance Show Prop where
    show (P s) = "P " ++ show s

-- Allows us to say "q" instead of P "q" or P {pname = "q"}
instance IsString Prop where
    fromString = P

data TruthTable a = TruthTable [a] [TruthTableRow] deriving (Eq, Show)
type TruthTableRow = ([Bool], Bool)

test36 :: Test
test36 = TestCase $ assertEqual "show propositional formula 1" expected input
    where input = List.map show fms
          expected = ["((P \"p\") .&. (P \"q\")) .|. (P \"r\")",
                      "(P \"p\") .&. ((P \"q\") .|. (P \"r\"))",
                      "((P \"p\") .&. (P \"q\")) .|. (P \"r\")"]
          fms :: [Formula Prop]
          fms = [p .&. q .|. r, p .&. (q .|. r), (p .&. q) .|. r]
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- Testing the parser and printer.

test01 :: Test
test01 = TestCase $ assertEqual "Build Formula 1" expected input
    where input = (Atom "p" .=>. Atom "q" .<=>. Atom "r" .&. Atom "s" .|. (Atom "t" .<=>. ((.~.) ((.~.) (Atom "u"))) .&. Atom "v"))
          expected = (Iff
                      (Imp
                       (Atom "p")
                       (Atom "q"))
                      (Or
                       (And (Atom "r") (Atom "s"))
                       (Iff (Atom "t")
                        (And (Not (Not (Atom "u"))) (Atom "v")))))

test02 :: Test
test02 = TestCase $ assertEqual "Build Formula 2" expected input
    where input = (Atom "fm" .&. Atom "fm")
          expected = (And (Atom "fm") (Atom "fm"))

test03 :: Test
test03 = TestCase $ assertEqual "Build Formula 3"
                                (Atom "fm" .|. Atom "fm" .&. Atom "fm")
                                (Or (Atom "fm") (And (Atom "fm") (Atom "fm")))

-- Example of use.

test04 :: Test
test04 = TestCase $ assertEqual "fixity tests" expected input
    where (input, expected) = unzip (List.map (\ (fm, flag) -> (eval fm v0, flag)) pairs)
          v0 x = error $ "Tests.Harrison.Prop.v0: " ++ show x
          pairs :: [(Formula String, Bool)]
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

-- | Interpretation of formulas.
eval :: Formula atom -> (atom -> Bool) -> Bool
eval fm v =
    case fm of
      False' -> False
      True' -> True
      Atom x -> v x
      Not p -> not (eval p v)
      And p q -> (eval p v) && (eval q v)
      Or p q -> (eval p v) || (eval q v)
      Imp p q -> not (eval p v) || (eval q v)
      Iff p q -> (eval p v) == (eval q v)
      Forall _x _p -> error "Forall in prop formula"
      Exists _x _p -> error "Exists in prop formula"

-- | Return the set of propositional variables in a formula.
atoms :: Ord atom => Formula atom -> Set atom
atoms fm = atom_union singleton fm

-- | Code to print out truth tables.
onallvaluations :: (Eq a, Ord a) => (r -> r -> r) -> ((a -> Bool) -> r) -> (a -> Bool) -> Set a -> r
onallvaluations combine subfn v ats =
    case minView ats of
      Nothing -> subfn v
      Just (p, ps) ->
          let v' t q = (if q == p then t else v q) in
          combine (onallvaluations combine subfn (v' False) ps) (onallvaluations combine subfn (v' True) ps)

truthTable :: forall atom. Ord atom => Formula atom -> TruthTable atom
truthTable fm =
    TruthTable atl (onallvaluations (<>) mkRow (const False) ats)
    where
      ats = atoms fm
      mkRow :: (atom -> Bool) -> [TruthTableRow]
      mkRow v = [(List.map v atl, eval fm v)]
      atl = Set.toAscList ats

-- | Recognizing tautologies.
tautology :: Ord atom => Formula atom -> Bool
tautology fm = onallvaluations (&&) (eval fm) (\_s -> False) (atoms fm)

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
unsatisfiable :: Ord atom => Formula atom -> Bool
unsatisfiable = tautology . Not
satisfiable :: Ord atom => Formula atom -> Bool
satisfiable = not . unsatisfiable

-- | Substitution operation.
psubst :: Ord atom => Map atom (Formula atom) -> Formula atom -> Formula atom
psubst subfn fm = onatoms (\ p -> maybe (Atom p) id (fpf subfn p)) fm

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
dual :: Formula atom -> Formula atom
dual fm =
  case fm of
    False' -> True'
    True' -> False'
    Atom _p -> fm
    Not p -> Not (dual p)
    And p q ->  Or (dual p) (dual q)
    Or p q -> And (dual p) (dual q)
    _ -> error"Formula involves connectives ==> or <=>"

-- Example.
test22 :: Test
test22 = TestCase $ assertEqual "Dual (p. 49)" expected input
    where input = dual (Atom (P "p") .|. ((.~.) (Atom (P "p"))))
          expected = And (Atom (P {pname = "p"})) (Not (Atom (P {pname = "p"})))

-- | Routine simplification.
psimplify1 :: Formula atom -> Formula atom
psimplify1 fm =
  case fm of
    Not False' -> True'
    Not True' -> False'
    Not (Not p) -> p
    And _p False' -> False'
    And False' _p -> False'
    And p True' -> p
    And True' p -> p
    Or p False' -> p
    Or False' p -> p
    Or _p True' -> True'
    Or True' _p -> True'
    Imp False' _p -> True'
    Imp _p True' -> True'
    Imp True' p -> p
    Imp p False' -> Not p
    Iff p True' -> p
    Iff True' p -> p
    Iff p False' -> Not p
    Iff False' p -> Not p
    _ -> fm

psimplify :: Formula atom -> Formula atom
psimplify fm =
  case fm of
    Not p -> psimplify1 (Not(psimplify p))
    And p q -> psimplify1 (And (psimplify p) (psimplify q))
    Or p q -> psimplify1 (Or (psimplify p) (psimplify q))
    Imp p q -> psimplify1 (Imp (psimplify p) (psimplify q))
    Iff p q -> psimplify1 (Iff (psimplify p) (psimplify q))
    _ -> fm

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

-- | Some operations on literals.
negative :: Formula atom -> Bool
negative (Not _) = True
negative _ = False

positive :: Formula atom -> Bool
positive = not . negative

negate :: Formula atom -> Formula atom
negate (Not p) = p
negate p = Not p

-- | Negation normal form.

nnf' :: Formula atom -> Formula atom
nnf' fm =
  case fm of
    And p q -> And (nnf p) (nnf q)
    Or p q -> Or (nnf p) (nnf q)
    Imp p q -> Or (nnf(Not p)) (nnf q)
    Iff p q -> Or (And(nnf p) (nnf q)) (And(nnf(Not p)) (nnf(Not q)))
    Not(Not p) -> nnf p
    Not(And p q) -> Or (nnf(Not p)) (nnf(Not q))
    Not(Or p q) -> And (nnf(Not p)) (nnf(Not q))
    Not(Imp p q) -> And (nnf p) (nnf(Not q))
    Not(Iff p q) -> Or (And (nnf p) (nnf (Not q))) (And (nnf (Not p)) (nnf q))
    _ -> fm

-- | Roll in simplification.
nnf :: Formula atom -> Formula atom
nnf = nnf' . psimplify

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

-- | Simple negation-pushing when we don't care to distinguish occurrences.
nenf' :: Formula atom -> Formula atom
nenf' fm =
  case fm of
    Not (Not p) -> nenf p
    Not (And p q) -> Or (nenf (Not p)) (nenf (Not q))
    Not (Or p q) -> And (nenf (Not p)) (nenf (Not q))
    Not (Imp p q) -> And (nenf p) (nenf (Not q))
    Not (Iff p q) -> Iff (nenf p) (nenf (Not q))
    And p q -> And (nenf p) (nenf q)
    Or p q -> Or (nenf p) (nenf q)
    Imp p q -> Or (nenf (Not p)) (nenf q)
    Iff p q -> Iff (nenf p) (nenf q)
    _ -> fm

nenf :: Formula atom -> Formula atom
nenf = nenf' . psimplify

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

-- | Disjunctive normal form (DNF) via truth tables.
list_conj :: Set (Formula atom) -> Formula atom
list_conj l = maybe true (\ (x, xs) -> Set.fold (.&.) x xs) (Set.minView l)

list_disj :: Set (Formula atom) -> Formula atom
list_disj l = maybe false (\ (x, xs) -> Set.fold (.|.) x xs) (Set.minView l)

mk_lits :: Ord atom => Set (Formula atom) -> (atom -> Bool) -> Formula atom
mk_lits pvs v = list_conj (Set.map (\ p -> if eval p v then p else Not p) pvs)

allsatvaluations :: Eq a => ((a -> Bool) -> Bool) -> (a -> Bool) -> Set a -> [a -> Bool]
allsatvaluations subfn v pvs =
    case Set.minView pvs of
      Nothing -> if subfn v then [v] else []
      Just (p, ps) -> (allsatvaluations subfn (\a -> if a == p then False else v a) ps) ++
                      (allsatvaluations subfn (\a -> if a == p then True else v a) ps)

dnf1 :: Ord atom => Formula atom -> Formula atom
dnf1 fm =
    list_disj (Set.fromList (List.map (mk_lits (Set.map atomic pvs)) satvals))
    where
      satvals = allsatvaluations (eval fm) (\_s -> False) pvs
      pvs = atoms fm

-- Examples.

test29 :: Test
test29 = TestCase $ assertEqual "dnf 1 (p. 56)" expected input
    where input = (dnf1 fm, truthTable fm)
          expected = ((r .&. (((.~.) p) .&. q)) .|. ((((.~.) q) .&. (((.~.) r) .&. p)) .|. (q .&. (((.~.) r) .&. p))),
                      (TruthTable
                       [P "p", P "q", P "r"]
                       [([False,False,False],False),
                        ([False,False,True],False),
                        ([False,True,False],False),
                        ([False,True,True],True),
                        ([True,False,False],True),
                        ([True,False,True],False),
                        ([True,True,False],True),
                        ([True,True,True],False)]))
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

test30 :: Test
test30 = TestCase $ assertEqual "dnf 2 (p. 56)" expected input
    where input = dnf1 (p .&. q .&. r .&. s .&. t .&. u .|. u .&. v :: Formula Prop)
          expected = (q .&. (r .&. (s .&. (t .&. (u .&. (((.~.) v) .&. p)))))) .|.
                      ((q .&. (r .&. (s .&. (u .&. (v .&. (((.~.) t) .&. p)))))) .|.
                       ((q .&. (r .&. (t .&. (u .&. (v .&. (((.~.) s) .&. p)))))) .|.
                        ((q .&. (r .&. (u .&. (v .&. (((.~.) s) .&. (((.~.) t) .&. p)))))) .|.
                         ((q .&. (s .&. (t .&. (u .&. (v .&. (((.~.) r) .&. p)))))) .|.
                          ((q .&. (s .&. (u .&. (v .&. (((.~.) r) .&. (((.~.) t) .&. p)))))) .|.
                           ((q .&. (t .&. (u .&. (v .&. (((.~.) r) .&. (((.~.) s) .&. p)))))) .|.
                            ((q .&. (u .&. (v .&. (((.~.) r) .&. (((.~.) s) .&. (((.~.) t) .&. p)))))) .|.
                             ((r .&. (s .&. (t .&. (u .&. (v .&. (((.~.) p) .&. q)))))) .|.
                              ((r .&. (s .&. (t .&. (u .&. (v .&. (((.~.) q) .&. p)))))) .|.
                               ((r .&. (s .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) t) .&. q)))))) .|.
                                ((r .&. (s .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) t) .&. p)))))) .|.
                                 ((r .&. (t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) s) .&. q)))))) .|.
                                  ((r .&. (t .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) s) .&. p)))))) .|.
                                   ((r .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) s) .&. (((.~.) t) .&. q)))))) .|.
                                    ((r .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) s) .&. (((.~.) t) .&. p)))))) .|.
                                     ((s .&. (t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. r)))))) .|.
                                      ((s .&. (t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) r) .&. q)))))) .|.
                                       ((s .&. (t .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) r) .&. p)))))) .|.
                                        ((s .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) t) .&. r)))))) .|.
                                         ((s .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) r) .&. (((.~.) t) .&. q)))))) .|.
                                          ((s .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) t) .&. p)))))) .|.
                                           ((t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) r) .&. s)))))) .|.
                                            ((t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) s) .&. r)))))) .|.
                                             ((t .&. (u .&. (v .&. (((.~.) p) .&. (((.~.) r) .&. (((.~.) s) .&. q)))))) .|.
                                              ((t .&. (u .&. (v .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) s) .&. p)))))) .|.
                                               ((u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) s) .&. t)))))) .|.
                                                ((u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) t) .&. s)))))) .|.
                                                 ((u .&. (v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) s) .&. (((.~.) t) .&. r)))))) .|.
                                                  ((u .&. (v .&. (((.~.) p) .&. (((.~.) r) .&. (((.~.) s) .&. (((.~.) t) .&. q)))))) .|.
                                                   ((u .&. (v .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) s) .&. (((.~.) t) .&. p)))))) .|.
                                                    ((v .&. (((.~.) p) .&. (((.~.) q) .&. (((.~.) r) .&. (((.~.) s) .&. (((.~.) t) .&. u)))))) .|.
                                                     (q .&. (r .&. (s .&. (t .&. (u .&. (v .&. p)))))))))))))))))))))))))))))))))))))
          [p, q, r, s, t, u, v] = List.map (Atom . P) ["p", "q", "r", "s", "t", "u", "v"]

-- | DNF via distribution.
distrib1 :: Formula atom -> Formula atom
distrib1 fm =
  case fm of
    And p (Or q r) -> Or (distrib1 (And p q)) (distrib1 (And p r))
    And (Or p q) r -> Or (distrib1 (And p r)) (distrib1 (And q r))
    _ -> fm

rawdnf :: Formula atom -> Formula atom
rawdnf fm =
  case fm of
    And p q -> distrib1 (And (rawdnf p) (rawdnf q))
    Or p q -> Or (rawdnf p) (rawdnf q)
    _ -> fm

-- Example.

test31 :: Test
test31 = TestCase $ assertEqual "rawdnf (p. 58)" expected input
    where input = rawdnf $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = ((atomic (P "p")) .&. ((.~.)(atomic (P "p"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "p")))) .|.
                     ((atomic (P "p")) .&. ((.~.)(atomic (P "r"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "r"))))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- | A version using a list representation.
distrib2 :: Ord a => Set (Set a) -> Set (Set a) -> Set (Set a)
distrib2 s1 s2 = allpairs union s1 s2

purednf :: Ord atom => Formula atom -> Set (Set (Formula atom))
purednf fm =
    case fm of
      And p q -> distrib2 (purednf p) (purednf q)
      Or p q -> union (purednf p) (purednf q)
      _ -> singleton (singleton fm)

-- Example.

test32 :: Test
test32 = TestCase $ assertEqual "purednf (p. 58)" expected input
    where input = purednf $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = Set.fromList [Set.fromList [p,Not p],
                                   Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p],
                                   Set.fromList [q,r,Not r]]
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- | Filtering out trivial disjuncts (in this guise, contradictory).
trivial :: Ord atom => Set (Formula atom) -> Bool
trivial lits =
    not . Set.null $ Set.intersection neg (Set.map Not pos)
    where (pos, neg) = Set.partition positive lits

-- Example.
test33 :: Test
test33 = TestCase $ assertEqual "trivial" expected input
    where input = Set.filter (not . trivial) (purednf fm)
          expected = Set.fromList [Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p]]
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- | With subsumption checking, done very naively (quadratic).
simpdnf :: Ord atom => Formula atom -> Set (Set (Formula atom))
simpdnf fm =
  if fm == False' then Set.empty else if fm == True' then singleton Set.empty else
  let djs = Set.filter (not . trivial) (purednf (nnf fm)) in
  Set.filter (\d -> not (setAny (\d' -> Set.isProperSubsetOf d' d) djs)) djs

-- | Mapping back to a formula.
dnf2 :: Ord atom => Formula atom -> Formula atom
dnf2 fm = list_disj (Set.map list_conj (simpdnf fm))

-- Example.

test34 :: Test
test34 = TestCase $ assertEqual "dnf" expected input
    where input = (dnf2 fm, tautology (Iff fm (dnf2 fm)))
          expected = (Or (And (Not r) p) (And r (And (Not p) q)), True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- | Conjunctive normal form (CNF) by essentially the same code.
purecnf :: Ord atom => Formula atom -> Set (Set (Formula atom))
purecnf fm = Set.map (Set.map Not) (purednf (nnf (Not fm)))

simpcnf :: Ord atom => Formula atom -> Set (Set (Formula atom))
simpcnf fm =
  if fm == False' then singleton (Set.empty) else if fm == True' then Set.empty else
  let cjs = Set.filter (not . trivial) (purecnf fm) in
  Set.filter (\c -> not (setAny (\c' -> Set.isProperSubsetOf c' c) cjs)) cjs

cnf :: Ord atom => Formula atom -> Formula atom
cnf fm = list_conj (Set.map list_disj (simpcnf fm))

-- Example.

test35 :: Test
test35 = TestCase $ assertEqual "cnf" expected input
    where input = (cnf fm, tautology (Iff fm (cnf fm)))
          -- Fully parenthesized
          -- expected = (((atomic (P "r")) .|. (atomic (P "p"))) .&. (((((.~.)(atomic (P "r")))) .|. (((.~.)(atomic (P "p"))))) .&. ((atomic (P "q")) .|. (atomic (P "p")))),True)
          -- Edited
          expected = ( (((.~.) ((.~.) (atomic (P "q")))) .|. ((.~.) ((.~.) (atomic (P "p")))))         .&.
                      ((((.~.) ((.~.) (atomic (P "r")))) .|. ((.~.) ((.~.) (atomic (P "p")))))        .&.
                              (((.~.) (atomic (P "r")))  .|. ((.~.) (atomic (P "p"))))),
                      True)
          -- expected = (And (Or q p) (And (Or r p) (Or (Not r) (Not p))),True)
          -- expected = (F, True)
          -- expected = (((atomic (P "r")) .|. (atomic (P "p"))) .&. (((((.~.)(atomic (P "r"))))) .|. ((((.~.)(atomic (P "p"))))) .&. (atomic (P "q")) .|. (atomic (P "p"))),True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

tests :: Test
tests = TestLabel "Prop" $ TestList [test36, test01, test02, test03, test04, {-test05,-}
                                     test06, test07, test08, test09, test10,
                                     test11, test12, test13, test14, test15,
                                     test16, test17, test18, test19, test20,
                                     test21, test22, test23, test24, test25,
                                     test26, test27, test28, test29, test30,
                                     test31, test32, test33, test34, test35]
