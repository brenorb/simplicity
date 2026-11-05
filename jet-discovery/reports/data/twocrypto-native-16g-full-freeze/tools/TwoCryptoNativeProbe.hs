{-# LANGUAGE GADTs #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_,unless)
import Data.List (isInfixOf)
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import qualified JetDiscovery.Corpus.TwoCrypto as TwoCrypto
import JetDiscovery.Run (VectorResult(..),progCmr,runVectors)
import JetDiscovery.Tx (hashToInteger)
import JetDiscovery.Types

native :: IO ()
native = case TwoCrypto.entry of
  Entry name _ _ _ _ _ program vectors -> do
    putStrLn name
    cmr <- evaluate (hashToInteger TwoCrypto.poolCmr)
    print ("canonical TwoCrypto CMR",cmr)
    case vectors of
      [] -> error "missing native TwoCrypto vectors"
      first:_ -> do
        let p = program (vecWitness first)
            h = progCmr p
            same = hashToInteger h == cmr && progCmr (Prog (unProg p)) == h
        print ("prepared and canonical CMR match",same)
        unless same (error "native TwoCrypto CMR mismatch")
        case boundView p of
          Just (BoundView k _) -> do
            let eligible = boundEligible k
            print ("pure bound kernel eligible",eligible)
            unless eligible (error "native TwoCrypto kernel ineligible")
          Nothing -> error "expected one bound witness"
        forM_ (runVectors program h vectors) $ \r -> do
          ok <- evaluate (vrOk r)
          print (vrName r,ok,vrNote r)
          unless (ok && "prepared" `isInfixOf` vrNote r)
            (error "native TwoCrypto vector or execution path mismatch")

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  case args of
    ["native"] -> native
    _ -> error "usage: TwoCryptoNativeProbe native"
