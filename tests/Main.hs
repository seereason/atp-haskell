import FOL (tests)
import Lib (tests)
import Prop (tests)
import Skolem (tests)
import Test.HUnit
import Extra (tests)

main :: IO Counts
main = runTestTT $ TestList [Lib.tests, Prop.tests, FOL.tests, Skolem.tests, Extra.tests]
