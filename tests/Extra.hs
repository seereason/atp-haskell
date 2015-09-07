{-# LANGUAGE GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
module Extra where

import FOL (vt, FOL(R), Term, HasEquality(equals), Predicate, fApp, (.=.), for_all, exists)
import Formulas
import Prop hiding (nnf)
import Skolem
import Test.HUnit

tests :: Test
tests = TestList [test06]

test06 :: Test
test06 =
    let fm :: Formula (FOL Predicate (Term Function V))
        fm = (.~.) (for_all "x" (vt "x" .=. vt "x") .=>. for_all "x" (exists "y" (vt "x" .=. vt "y")))
        expected :: Formula (FOL Predicate (Term Function V))
        expected = (vt "x" .=. vt "x") .&. ((.~.) (fApp (Skolem (V "x")) [] .=. vt "x"))
        sk = runSkolem (skolemize fm) :: Formula (FOL Predicate (Term Function V))
        table = truthTable expected :: TruthTable (FOL Predicate (Term Function V)) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y"
                           (expected :: Formula (FOL Predicate (Term Function V)),
                            TruthTable
                              [R equals [vt "x", fApp (Skolem (V "y")) [vt "x"]],
                               R equals [fApp (Skolem (V "x")) [], fApp (Skolem (V "x")) []]]
                              [([False,False],True),
                               ([False,True],False),
                               ([True,False],True),
                               ([True,True],True)] :: TruthTable (FOL Predicate (Term Function V)))
                           (sk, table)

{-
test12 :: Test
test12 =
    let fm = (let (x, y) = (vt "x" :: Term, vt "y" :: Term) in ((for_all "x" ((x .=. x))) .=>. (for_all "x" (exists "y" ((x .=. y))))) :: Formula FOL) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y" (holds fm) True
-}
