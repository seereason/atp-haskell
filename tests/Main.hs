import Test.HUnit

import FOL (testFOL)
import Herbrand (testHerbrand)
import Lib (testLib)
import Prop (testProp)
import PropExamples (testPropExamples)
import DefCNF (testDefCNF)
import DP (testDP)
import Skolem (testSkolem)
import Unif (testUnif)
import Tableaux (testTableaux)
import Resolution (testResolution)
import Prolog (testProlog)
import Meson (testMeson)
import Extra (testExtra)

main :: IO Counts
main = runTestTT $ TestList [testLib,
                             testProp,
                             testPropExamples,
                             testDefCNF,
                             testDP,
                             testFOL,
                             -- testEqual,
                             testSkolem,
                             testHerbrand,
                             testUnif,
                             testTableaux,
                             testResolution,
                             testProlog,
                             testMeson,
                             testExtra]
