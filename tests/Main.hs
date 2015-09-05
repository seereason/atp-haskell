import FOL (tests)
import Lib (tests)
import Prop (tests)
import Test.HUnit

main = runTestTT $ TestList [Lib.tests, Prop.tests, FOL.tests]
