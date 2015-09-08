import FOL (tests)
import Lib (tests)
import Prop (tests)
import PropExamples (tests)
import DefCNF (tests)
import Skolem (tests)
import Test.HUnit
import Extra (tests)

main :: IO Counts
main = runTestTT $ TestList [Lib.tests, Prop.tests, PropExamples.tests, DefCNF.tests, FOL.tests, Skolem.tests, Extra.tests]
