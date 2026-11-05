module Main where
import qualified JetDiscovery.Ref.FibonacciStark as F
import Control.Exception (evaluate)
import System.CPUTime (getCPUTime)
import System.IO (hFlush, stdout)
import GHC.Stats (getRTSStats, max_live_bytes, allocated_bytes)

phase label action = do
  putStrLn (label ++ " starting")
  hFlush stdout
  a <- getCPUTime
  value <- action
  b <- getCPUTime
  stats <- getRTSStats
  putStrLn (label ++ " result=" ++ show value ++ " cpu_seconds=" ++ show (fromIntegral (b-a)/1e12 :: Double) ++ " max_live_bytes=" ++ show (max_live_bytes stats) ++ " allocated_bytes=" ++ show (allocated_bytes stats))
  hFlush stdout
main = do
  let p = F.realistic
      pr = F.prove p
  phase "prove/show-force" (evaluate (length (show pr)))
  phase "verify" (evaluate (F.verify p pr))
