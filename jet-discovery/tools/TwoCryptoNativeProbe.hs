{-# LANGUAGE GADTs #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_,unless)
import Data.List (isInfixOf)
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import qualified JetDiscovery.Corpus.TwoCrypto as TwoCrypto
import JetDiscovery.Run (VectorResult(..),runVectors)
import JetDiscovery.Tx (hashToInteger)
import JetDiscovery.Types

native :: IO ()
native = case TwoCrypto.entry of
  Entry name _ _ _ _ _ program vectors -> do
    putStrLn name
    cmr <- evaluate (hashToInteger TwoCrypto.poolCmr)
    print ("canonical TwoCrypto CMR",cmr)
    let canonical = 0xfbcdcf5cd9b0d3a6b7dea641b85de4c02eafa5ce9e7c7d3879071a00a8602a31
    print ("matches the previously compared ordinary-program CMR",cmr==canonical)
    unless (cmr==canonical) (error "native TwoCrypto canonical CMR changed")
    case vectors of
      [] -> error "missing native TwoCrypto vectors"
      first:_ -> do
        let p = program (vecWitness first)
        case boundView p of
          Just (BoundView k _) -> do
            let eligible = boundEligible k
            print ("pure bound kernel eligible",eligible)
            unless eligible (error "native TwoCrypto kernel ineligible")
          Nothing -> error "expected one bound witness"
        forM_ (runVectors program TwoCrypto.poolCmr vectors) $ \r -> do
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
