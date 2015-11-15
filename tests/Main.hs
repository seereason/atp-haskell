import Test.HUnit

import Data.Logic.ATP.DefCNF (testDefCNF)
import Data.Logic.ATP.DP (testDP)
import Data.Logic.ATP.FOL (testFOL)
import Data.Logic.ATP.Herbrand (testHerbrand)
import Data.Logic.ATP.Lib (testLib)
import Data.Logic.ATP.Prop (testProp)
import Data.Logic.ATP.PropExamples (testPropExamples)
import Data.Logic.ATP.Skolem (testSkolem)
import Data.Logic.ATP.ParserTests (testParser)
import Data.Logic.ATP.Unif (testUnif)
import Data.Logic.ATP.Tableaux (testTableaux)
import Data.Logic.ATP.Resolution (testResolution)
import Data.Logic.ATP.Prolog (testProlog)
import Data.Logic.ATP.Meson (testMeson)
import Data.Logic.ATP.Equal (testEqual)
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
