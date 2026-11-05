{-# LANGUAGE GADTs #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_,unless)
import Data.List (isInfixOf)
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import qualified JetDiscovery.Corpus.NexusMutual as Nexus
import JetDiscovery.Run (VectorResult(..),progCmr,runVectors)
import JetDiscovery.Tx (hashToInteger)
import JetDiscovery.Types

native :: IO ()
native = case Nexus.entry of
  Entry name _ _ _ _ _ program vectors -> do
    putStrLn name
    cmr <- evaluate (hashToInteger Nexus.mutualCmr)
    print ("canonical mutual CMR",cmr)
    case vectors of
      [] -> error "missing native mutual vectors"
      first:_ -> do
        let p = program (vecWitness first)
            h = progCmr p
            same = hashToInteger h == cmr && progCmr (Prog (unProg p)) == h
        print ("prepared and canonical CMR match",same)
        unless same (error "native mutual CMR mismatch")
        case boundView p of
          Just (BoundView k _) -> do
            let eligible = boundEligible k
            print ("pure bound kernel eligible",eligible)
            unless eligible (error "native mutual kernel ineligible")
          Nothing -> error "expected one bound witness"
        forM_ (runVectors program h vectors) $ \r -> do
          ok <- evaluate (vrOk r)
          print (vrName r,ok,vrNote r)
          unless (ok && "prepared" `isInfixOf` vrNote r)
            (error "native mutual vector or execution path mismatch")

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  case args of
    ["reference"] -> do
      print ("independent Integer mutual lifecycle",Nexus.referenceAudit)
      unless Nexus.referenceAudit (error "independent reference audit failed")
    ["native"] -> native
    _ -> error "usage: NexusMutualProbe reference|native"
