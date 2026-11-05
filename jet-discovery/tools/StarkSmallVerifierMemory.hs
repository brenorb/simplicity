-- Standalone diagnostic; intentionally outside the corpus/build configuration.
-- Compile using the built jet-discovery package DB (see STARK-DIAGNOSTICS.md).
module Main where

import qualified JetDiscovery.Ref.FibonacciStark as F
import qualified JetDiscovery.Corpus.FibonacciStark as C
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
import JetDiscovery.Cost (TermWeight, milliWeigh)
import Simplicity.MerkleRoot (CommitmentRoot, commitmentRoot)
import Control.Exception (evaluate)
import System.Environment (getArgs)
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
  args <- getArgs
  let (p, phases) = case break (== "--") args of
        ([q,t,d], _:rest) -> (F.Parameters (read t) (read d) (read q), rest)
        _ -> (F.small, args)
      wanted name = null phases || name `elem` phases
      pr = F.prove p
      program = Prog (C.verifier p pr)
      measured = measure program
      env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  phase "reference" (evaluate (F.verify p pr))
  if wanted "rawcmr" then phase "rawcmr" (evaluate (commitmentRoot (C.verifier p pr :: CommitmentRoot () ()))) else pure ()
  if wanted "rawcost" then phase "rawcost" (evaluate (milliWeigh (C.verifier p pr :: TermWeight () ()))) else pure ()
  if wanted "cmr" then phase "cmr" (evaluate (mCmr measured)) else pure ()
  if wanted "cost" then phase "cost" (evaluate (mCost measured)) else pure ()
  if wanted "baseline" then phase "baseline" (evaluate (mCostBase measured)) else pure ()
  if wanted "whatif" then phase "whatif" (evaluate (mCostWhatIf measured)) else pure ()
  if wanted "bits" then phase "bits" (evaluate (mProgBits measured + mWitBits measured)) else pure ()
  if wanted "profile" then phase "profile" (evaluate (mProfileTotal measured)) else pure ()
  if wanted "candidates" then phase "candidates" (evaluate (length (mWhatIfJets measured))) else pure ()
  if wanted "ablations" then phase "ablations" (evaluate (sum (map snd (mAblations measured)))) else pure ()
  if wanted "eval" then phase "eval" (evaluate (vrOk (runVector (\proof -> Prog (C.verifier p proof)) (mCmr measured) (Vector "honest" env pr Accept)))) else pure ()
