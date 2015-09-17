{-# LANGUAGE GADTs, MultiParamTypeClasses, OverloadedStrings, ScopedTypeVariables #-}
module Extra where

import Control.Applicative.Error (Failing(Failure, Success))
import Data.List as List (map)
import Data.Map as Map (fromList)
import Data.Set as Set (fromList, map, Set)
import Test.HUnit

import FOL (vt, fApp, (.=.), pApp, for_all, exists, HasPredicate(applyPredicate), Predicate(Equals))
import Formulas
import Lib (failing)
import Meson (meson)
import Pretty (prettyShow)
import Prop hiding (nnf)
import Skolem (HasSkolem(toSkolem), skolemize, runSkolem, MyAtom, MyFormula, MyTerm)
import Tableaux (Depth(Depth))

tests :: Test
tests = TestList [test06, test07]

test06 :: Test
test06 =
    let fm :: MyFormula
        fm = for_all "x" (vt "x" .=. vt "x") .=>. for_all "x" (exists "y" (vt "x" .=. vt "y"))
        expected :: MyFormula
        expected =  (vt "x" .=. vt "x") .&. ((.~.) (fApp (toSkolem "x") [] .=. vt "x"))
        -- atoms = [applyPredicate equals [(vt ("x" :: V)) (vt "x")] {-, (fApp (toSkolem "x")[]) .=. (vt "x")-}] :: [MyAtom]
        sk = runSkolem (skolemize id ((.~.) fm)) :: MyFormula
        table = truthTable sk :: TruthTable MyAtom in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y"
                           (expected,
                            TruthTable
                              [applyPredicate Equals [vt "x", vt "x"], applyPredicate Equals [fApp (toSkolem "x")[], vt "x"]]
                              [([False,False],False),
                               ([False,True],False),
                               ([True,False],True),
                               ([True,True],False)] :: TruthTable MyAtom,
                           Set.fromList [Success ((Map.fromList [("_0",vt "_1"),
                                                                 ("_1",fApp (toSkolem "x")[])],
                                                   0,
                                                   2),
                                                  Depth 1)])
                           (sk, table, runSkolem (meson Nothing fm))

mesonTest :: MyFormula -> Set (Failing Depth) -> Test
mesonTest fm expected =
    let me = Set.map (failing Failure (Success . snd)) (runSkolem (meson (Just (Depth 1000)) fm)) in
    TestCase $ assertEqual ("MESON test: " ++ prettyShow' fm) expected me

fms :: [(MyFormula, Set (Failing Depth))]
fms = [ -- if x every x equals itself then there is always some y that equals x
        let [x, y] = [vt "x", vt "y"] :: [MyTerm] in
        (for_all "x" (x .=. x) .=>. for_all "x" (exists "y" (x .=. y)),
         Set.fromList [Success (Depth 1)]),
        -- Socrates is a human, all humans are mortal, therefore socrates is mortal
        let x = vt "x" :: MyTerm
            [s, h, m] = [pApp "S", pApp "H", pApp "M"] :: [[MyTerm] -> MyFormula] in
        ((for_all "x" (s [x] .=>. h [x]) .&. for_all "x" (h [x] .=>. m [x])) .=>. for_all "x" (s [x] .=>. m [x]),
         Set.fromList [Success (Depth 3)]) ]

test07 :: Test
test07 = TestList (List.map (uncurry mesonTest) fms)

{-
test12 :: Test
test12 =
    let fm = (let (x, y) = (vt "x" :: Term, vt "y" :: Term) in ((for_all "x" ((x .=. x))) .=>. (for_all "x" (exists "y" ((x .=. y))))) :: Formula FOL) in
    TestCase $ assertEqual "∀x. x = x ⇒ ∀x. ∃y. x = y" (holds fm) True
-}
