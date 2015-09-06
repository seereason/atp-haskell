{-# LANGUAGE GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
module Extra where

import FOL (vt, Term(Var), FOLEQ((:=:)), fvFOLEQ, mapTermsFOLEQ, fApp, (.=.))
import Formulas
import Prop hiding (nnf)
import Skolem
import Test.HUnit

tests :: Test
tests = TestList [test06]

test06 :: Test
test06 =
    let fm = (.~.) (for_all "x" (vt "x" .=. vt "x") .=>. for_all "x" (exists "y" (vt "x" .=. vt "y")))
        expected = Atom (Var (V "x") :=: Var (V "x")) .&. ((.~.) (Atom (fApp (Skolem (V "x")) [] :=: Var (V "x"))))
        sk = runSkolem (skolemize fvFOLEQ mapTermsFOLEQ id fm) :: Formula (FOLEQ String Function)
        table = truthTable expected :: TruthTable (FOLEQ String Function) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y"
                           (expected,
                            TruthTable
                              [Var (V "x") :=: fApp (Skolem (V "y")) [Var (V "x")],
                               fApp (Skolem (V "x")) [] :=: fApp (Skolem (V "x")) []]
                              [([False,False],True),
                               ([False,True],False),
                               ([True,False],True),
                               ([True,True],True)])
                           (sk, table)

{-
test12 :: Test
test12 =
    let fm = (let (x, y) = (vt "x" :: Term, vt "y" :: Term) in ((for_all "x" ((x .=. x))) .=>. (for_all "x" (exists "y" ((x .=. y))))) :: Formula FOLEQ) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y" (holds fm) True
-}
