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
import Equal (testEqual)
import Extra (testExtra)

import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))

main :: IO Counts
main = runTestTT (TestList  [testLib,
                             testProp,
                             testPropExamples,
                             testDefCNF,
                             testDP,
                             testFOL,
                             testSkolem,
                             testHerbrand,
                             testUnif,
                             testTableaux,
                             testResolution,
                             testProlog,
                             testMeson,
                             testEqual,
                             testExtra]) >>= doCounts
    where
      doCounts counts' = exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
