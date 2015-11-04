import Test.HUnit

import DefCNF (testDefCNF)
import DP (testDP)
import FOL (testFOL)
import Herbrand (testHerbrand)
import Lib (testLib)
import Prop (testProp)
import PropExamples (testPropExamples)
import Skolem (testSkolem)
import ParserTests (testParser)
import Unif (testUnif)
import Tableaux (testTableaux)
import Resolution (testResolution)
import Prolog (testProlog)
import Meson (testMeson)
import Equal (testEqual)
import Extra (testExtra)

import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))

main :: IO Counts
main = runTestTT (TestList  [TestLabel "Lib" testLib,
                             TestLabel "Prop" testProp,
                             TestLabel "PropExamples" testPropExamples,
                             TestLabel "DefCNF" testDefCNF,
                             TestLabel "DP" testDP,
                             TestLabel "FOL" testFOL,
                             TestLabel "Skolem" testSkolem,
                             TestLabel "Parser" testParser,
                             TestLabel "Herbrand" testHerbrand,
                             TestLabel "Unif" testUnif,
                             TestLabel "Tableaux" testTableaux,
                             TestLabel "Resolution" testResolution,
                             TestLabel "Prolog" testProlog,
                             TestLabel "Meson" testMeson,
                             TestLabel "Equal" testEqual,
                             TestLabel "Extra" testExtra
                             ]) >>= doCounts
    where
      doCounts counts' = exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
