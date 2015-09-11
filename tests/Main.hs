import FOL (tests)
import Herbrand (tests)
import Lib (tests)
import Prop (tests)
import PropExamples (tests)
import DefCNF (tests)
import DP (tests)
import Skolem (tests)
import Unif (tests)
import Tableaux (tests)
import Test.HUnit
import Extra (tests)

main :: IO Counts
main = runTestTT $ TestList [Lib.tests, Prop.tests, PropExamples.tests, DefCNF.tests, DP.tests, FOL.tests,
                             Skolem.tests, Herbrand.tests, Unif.tests, Tableaux.tests, Extra.tests]
