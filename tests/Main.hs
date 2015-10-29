import Test.HUnit

import FOL (testFOL)
import Herbrand (testHerbrand)
import Lib (testLib)
import Prop (testProp)
import PropExamples (testPropExamples)
import DefCNF (testDefCNF)
import DP (testDP)
import Skolem (testSkolem, runSkolem)
import Unif (testUnif)
import Tableaux (testTableaux)
import Resolution (testResolution)
import Prolog (testProlog)
import Meson (testMeson, meson)
import Equal (testEqual, equalitize, wishnu)
import Extra (testExtra)

import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))
import System.CPUTime (getCPUTime)
import Text.Printf
import Control.Concurrent
import Control.Exception
import Data.Time.Clock -- (DiffTime, getCurrentTime, UTCTime)

time :: IO t -> IO t
time a = do
  start <- getCurrentTime
  v <- a
  end <- getCurrentTime
  putStrLn $ "Computation time: " ++ show (diffUTCTime end start)
  return v

compete :: [IO a] -> IO a
compete actions = do
  mvar <- newEmptyMVar
  tids <- mapM (\action -> forkIO $ action >>= putMVar mvar) actions
  result <- takeMVar mvar
  mapM_ killThread tids
  return result

timeout :: DiffTime -> IO t -> IO (Either String t)
timeout delay a = do
  compete [(threadDelay . fromEnum . realToFrac $ delay / 1e6) >> return (Left "timeout"),
           Right <$> a]

timeoutIterate :: DiffTime -> (b -> b) -> b -> IO b
timeoutIterate interval f x = do
  t <- getCurrentTime
  timeoutIterate' (addUTCTime (realToFrac interval) t) f x

timeoutIterate' :: UTCTime -> (b -> b) -> b -> IO b
timeoutIterate' fin f x = do
  t <- getCurrentTime
  if t > fin then
      return x
    else
      do y <- evaluate (f x)
         t' <- getCurrentTime
         timeoutIterate' fin f y

main :: IO Counts
main = -- print (runSkolem (meson Nothing (equalitize wishnu))) >>
       runTestTT (TestList  [testLib,
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
