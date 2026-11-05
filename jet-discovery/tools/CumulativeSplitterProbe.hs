{-# LANGUAGE RankNTypes #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import JetDiscovery.Corpus.CumulativeSplitter (entries,referenceAudit)
import JetDiscovery.Run (VectorResult(..),progCmr,runVectors)
import JetDiscovery.Types

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  unless referenceAudit exitFailure
  putStrLn "independent cumulative balance, rounding, cap and all six release orders: PASS"
  case entries of
    [Entry ident _ _ _ _ _ make vs] -> do
      let p = make (vecWitness (head vs))
          cmr = progCmr p
          prepared = case boundView p of Just (BoundView k _) -> boundEligible k; _ -> False
      putStrLn (ident ++ " vectors=" ++ show (length vs) ++ " prepared=" ++ show prepared ++ " CMR=" ++ show cmr)
      ok <- forM (runVectors make cmr vs) $ \r -> do
        pass <- evaluate (vrOk r)
        putStrLn (vrName r ++ ": " ++ show pass ++ " (" ++ vrNote r ++ ")")
        pure pass
      unless (length vs == 28 && prepared && and ok) exitFailure
    _ -> exitFailure
