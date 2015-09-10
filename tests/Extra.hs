{-# LANGUAGE GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
module Extra where

import FOL (vt, fApp, (.=.), for_all, exists, IsAtom(appAtom), Predicate(Equals))
import Formulas
import Prop hiding (nnf)
import Skolem (HasSkolem(toSkolem), skolemize, runSkolem, MyAtom, MyFormula)
import Test.HUnit

tests :: Test
tests = TestList [test06]

test06 :: Test
test06 =
    let fm :: MyFormula
        fm = (.~.) (for_all "x" (vt "x" .=. vt "x") .=>. for_all "x" (exists "y" (vt "x" .=. vt "y")))
        expected :: MyFormula
        expected = (vt "x" .=. vt "x") .&. ((.~.) (fApp (toSkolem "x") [] .=. vt "x"))
        expected' :: MyFormula
        expected' = (((vt "x") .=. (vt "x"))) .&. ((.~.) (((fApp (toSkolem "x")[]) .=. (vt "x"))))
        -- atoms = [appAtom equals [(vt ("x" :: V)) (vt "x")] {-, (fApp (toSkolem "x")[]) .=. (vt "x")-}] :: [MyAtom]
        sk = runSkolem (skolemize id fm) :: MyFormula
        table = truthTable expected' :: TruthTable MyAtom in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y"
                           (expected',
                            TruthTable
                              [appAtom Equals [vt "x", vt "x"],appAtom Equals [fApp (toSkolem "x")[], vt "x"]]
                              [([False,False],False),
                               ([False,True],False),
                               ([True,False],True),
                               ([True,True],False)] :: TruthTable MyAtom)
                           (sk, table)

{-
test12 :: Test
test12 =
    let fm = (let (x, y) = (vt "x" :: Term, vt "y" :: Term) in ((for_all "x" ((x .=. x))) .=>. (for_all "x" (exists "y" ((x .=. y))))) :: Formula FOL) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y" (holds fm) True
-}
