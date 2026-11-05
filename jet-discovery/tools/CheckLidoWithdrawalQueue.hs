-- The CMR mode uses a typed dummy witness, so signatures cannot create a
-- second copy of the whole inferred program during fixture construction.
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM, unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import qualified JetDiscovery.Corpus.NativeLidoQueue as Queue
import JetDiscovery.Run (VectorResult(..), progCmr, runVectors)
import JetDiscovery.Types

main :: IO ()
main = do
  args <- getArgs
  case (args, Queue.entries) of
    (["cmr"], [_]) -> do
      let cmr = show (G.cmrOf Queue.queueT)
      say "START canonical typed dummy"
      _ <- evaluate (length cmr)
      say ("CMR " ++ cmr)
    (["vectors", fixture], [Entry ident _ _ _ _ _ program vectors]) -> do
      first <- case vectors of
        vector : _ -> pure vector
        [] -> fail "Lido queue has no vectors"
      say ("START canonical " ++ ident)
      let cmr = progCmr (program (vecWitness first))
      unless (show cmr == fixture) (fail ("independent fixture CMR mismatch: " ++ show cmr))
      say ("CMR " ++ show cmr ++ " fixture parity=True")
      results <- forM (runVectors program cmr vectors) $ \r -> do
        say (ident ++ "\t" ++ vrName r ++ "\t" ++ show (vrOk r) ++ "\t" ++ vrNote r)
        pure (vrOk r)
      say ("TOTAL " ++ show (length results) ++ " vectors, "
           ++ show (length (filter not results)) ++ " failures")
      unless (and results) exitFailure
    _ -> fail "usage: CheckLidoWithdrawalQueue cmr | vectors EXPECTED_0x_CMR"
 where
  say line = putStrLn line >> hFlush stdout
