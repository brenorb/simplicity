module Main where
import Control.Monad (unless)
import System.Exit (exitFailure)
import JetDiscovery.Regression.WitnessState (stateAliasChecks)
main :: IO ()
main=do
 mapM_ print stateAliasChecks
 unless (all snd stateAliasChecks) exitFailure
