-- Exercise the real registered predicates with the same witness and CMR at
-- 16 and 17 actual inputs. The legacy mode documents the original bypass.
module Main where

import Control.Monad (forM, unless)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Word (Word32, Word64)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified JetDiscovery.Corpus.Aggregate as Aggregate
import JetDiscovery.Lib.State (stateScript, stateTap)
import qualified JetDiscovery.Ref.Bip340 as Ref
import JetDiscovery.Run (VectorResult(..), progCmr, runVector)
import JetDiscovery.Tx (dummyOutpoint, mkEnv, mkInput, mkOutput, mkTx, unhex)
import JetDiscovery.Types

data Case = Case String Word32 [(Word64, Bool)] Word64 Expect

main :: IO ()
main = do
  args <- getArgs
  let overBound = case args of
        ["legacy"] -> Accept
        ["guarded"] -> Reject
        _ -> error "usage: CheckAggregateInputBound legacy|guarded"
  results <- forM Aggregate.entries $ \entry -> checkEntry overBound entry
  let outcomes = concat results
  putStrLn ("TOTAL " ++ show (length outcomes) ++ " vectors, "
           ++ show (length (filter not outcomes)) ++ " failures")
  unless (and outcomes) exitFailure

checkEntry :: Expect -> Entry -> IO [Bool]
checkEntry overBound (Entry ident _ _ _ _ _ program fixtures) = do
  first <- case fixtures of
    vector : _ -> pure vector
    [] -> fail "aggregate entry has no witness fixture"
  let witness = vecWitness first
      cmr = progCmr (program witness)
      payout = case ident of
        "bip443-ccv-aggregate" -> ccvPayout
        "app-vault-batch-recover" -> unhex "0014" <> BS.replicate 20 9
        _ -> error ("unexpected entry " ++ ident)
      boundary (Case name current inputs paid expected) =
        Vector name (environment payout current inputs paid) witness expected
      cases =
        [ Case "16 same-script inputs; last input executes" 15 (matching 16) 16000 Accept
        , Case "16 same-script inputs; output one satoshi short" 15 (matching 16) 15999 Reject
        , Case "16 inputs; unrelated input excluded from sum" 14
               (matching 15 ++ [(1000, False)]) 15000 Accept
        , Case "17 same-script inputs; first input ignores last 1000 sats" 0
               (matching 17) 16000 overBound
        , Case "17 same-script inputs; last input ignores its own 1000 sats" 16
               (matching 17) 16000 overBound
        , Case "17 same-script inputs; fully funded but outside the admitted bound" 0
               (matching 17) 17000 overBound
        ]
  putStrLn (ident ++ " CMR " ++ show cmr)
  forM (fixtures ++ map boundary cases) $ \vector -> do
    let result = runVector program cmr vector
    putStrLn (ident ++ "\t" ++ vrName result ++ "\t" ++ vrNote result
             ++ "\t" ++ if vrOk result then "PASS" else "FAIL")
    pure (vrOk result)
 where
  matching count = replicate count (1000, True)

ccvPayout :: BS.ByteString
ccvPayout = unhex "5120" <> Ref.bytesFromInt (Ref.taprootTweak embedded root)
 where
  sk = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
  embedded = Ref.embedData (Ref.pubkeyOf sk) (BS.replicate 32 0x11)
  root = BS.replicate 32 0x22

environment payout current inputs paid cmr =
  mkEnv (mkTx 2 (zipWith input [0..] inputs) [mkOutput paid payout] 0)
        current (\root -> stateTap root stateData) cmr
 where
  stateData = BS.replicate 32 0x42
  covenant = stateScript cmr stateData
  unrelated = unhex "0014" <> BS.replicate 20 0x55
  input ix (amount, matches) = mkInput (dummyOutpoint ix) amount
    (BL.fromStrict (if matches then covenant else unrelated)) 0xfffffffe
