module Main where

import Control.Exception (evaluate)
import Control.Monad (forM, unless)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import GHC.Stats (RTSStats(..), getRTSStats)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import System.Mem (performGC)
import qualified JetDiscovery.Corpus.NativeV3Pool as V
import qualified JetDiscovery.Lib.ClaimLedger as C
import JetDiscovery.Run (VectorResult(..), progCmr, runVectors)
import JetDiscovery.Types

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["cmr"] -> run Nothing
    ["vectors", expected] -> run (Just expected)
    _ -> error "usage: CheckV3Native cmr | vectors EXPECTED_0x_CMR"

run :: Maybe String -> IO ()
run expected =
  case V.v3Entry of
    Entry ident _ _ _ _ _ program vectors -> do
      say ("START canonical " ++ ident)
      begin <- getCurrentTime
      let cmr = case expected of
            Nothing -> C.cmrOf V.v3T
            Just _ -> case vectors of
              first : _ -> progCmr (program (vecWitness first))
              [] -> error "empty concentrated pool vector set"
      _ <- evaluate (length (show cmr))
      say ("CMR " ++ ident ++ " " ++ show cmr)
      performGC
      stats <- getRTSStats
      end <- getCurrentTime
      say ("END canonical " ++ ident ++ " elapsed=" ++ show (diffUTCTime end begin)
           ++ " max_live_bytes=" ++ show (max_live_bytes stats)
           ++ " allocated_bytes=" ++ show (allocated_bytes stats))
      case expected of
        Nothing -> pure ()
        Just fixture -> do
          unless (show cmr == fixture) (error "independent fixture CMR mismatch")
          say (ident ++ ": fixture parity=True; preparing bound vector execution")
          oks <- forM (runVectors program cmr vectors) $ \result -> do
            say (ident ++ "\t" ++ vrName result ++ "\t" ++ show (vrOk result)
                 ++ "\t" ++ vrNote result)
            pure (vrOk result)
          say ("TOTAL: 1 groups, " ++ show (length oks) ++ " vectors, "
               ++ (if and oks then "0" else "1") ++ " failed groups")
          unless (and oks) exitFailure
  where
    say line = putStrLn line >> hFlush stdout
