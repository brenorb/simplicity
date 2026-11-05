{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -O0 #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM, unless)
import qualified Data.ByteString.Lazy as BL
import Data.List (find)
import Data.Serialize (runPut)
import qualified Data.Vector as V
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.FFI.Jets as C
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import Simplicity.Digest (Hash256)
import Simplicity.Ty.Word (fromWord16)
import qualified JetDiscovery.Corpus.SnapshotGovernor as Gov
import JetDiscovery.Lib.Bytes (w16, w32, w64, w256FromBytes)
import qualified JetDiscovery.Ref.SnapshotGovernor as Ref
import JetDiscovery.Run (VectorResult(..), progCmr, runVectors)
import JetDiscovery.Tx
import JetDiscovery.Types
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdout)

assert :: String -> Bool -> IO ()
assert name passed = do
  putStrLn (name ++ "=" ++ show passed)
  unless passed exitFailure

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  checkQuorum
  checkSnapshotReference
  case Gov.entry of
    Entry ident _ _ _ _ _ make vectors -> do
      let first = make (vecWitness (head vectors))
          cmr = progCmr first
          eligible = case boundView first of
            Just (BoundView kernel _) -> boundEligible kernel
            Nothing -> False
      _ <- evaluate eligible
      putStrLn (ident ++ " vectors=" ++ show (length vectors) ++ " prepared_kernel_eligible=" ++ show eligible ++ " CMR=" ++ show cmr)
      passed <- forM (runVectors make cmr vectors) $ \result -> do
        ok <- evaluate (vrOk result)
        putStrLn (vrName result ++ " expected=" ++ show (vrExpect result) ++ " actual=" ++ vrNote result ++ " pass=" ++ show ok)
        return ok
      assert "all 63 actual governance vectors pass at one canonical CMR" (eligible && length vectors == 63 && and passed)
      checkWireChain cmr (filter ((== Accept) . vecExpect) vectors)

checkQuorum :: IO ()
checkQuorum = do
  let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 BL.empty 0xfffffffe] [mkOutput 999 (unhex "51")] 0)
        0 defaultTap (hashFromInteger 1)
      supplies = [0..3] ++ [298..303] ++ [32768,65535]
      evaluator = J.unwrap (J.jetSubst Gov.quorum)
      quorum supply = fromWord16 <$> J.fastEval evaluator env (w16 supply)
  assert "native floor matches the Integer formula at all 12 sampled supplies"
    (length supplies == 12 && all (\supply -> quorum supply == Just (Ref.quorum supply)) supplies)
  assert "301 units at 40 percent floor to 120, while 303 units require 121"
    (quorum 301 == Just 120 && quorum 303 == Just 121)

checkSnapshotReference :: IO ()
checkSnapshotReference = do
  let apply state action = case Ref.step state action 1 of
        Just [Ref.Continue next] -> next
        _ -> error "expected governance reference continuation"
      before = foldl apply Ref.initial [Ref.Transfer 0 2 31, Ref.Transfer 1 2 50, Ref.Delegate 2 3]
      proposed = apply before (Ref.Propose 2 0 25001)
      changed = foldl apply proposed [Ref.Transfer 0 1 20, Ref.Delegate 1 0]
      counted = foldl apply changed [Ref.Vote 0 1, Ref.Vote 1 2, Ref.Tick, Ref.Vote 2 0]
  assert "prior checkpoint is 70,50,0 while current delegated power becomes 120,0,0"
    (Ref.weights proposed == [70,50,0] && Ref.weights changed == [70,50,0] && Ref.power changed == [120,0,0])
  assert "all three ballot bits are set and exact 70-for plus 50-abstain reaches quorum"
    (Ref.voted counted == 7 && Ref.tallies counted == [0,70,50] && Ref.expired counted && Ref.successful counted)

checkWireChain :: Hash256 -> [Vector w] -> IO ()
checkWireChain cmr vectors = do
  previous <- foldM check [] vectors
  assert "all 30 positive raw-wire and linked fixtures checked" (length previous == 30)
 where
  pointKey point = (D.opHash point, D.opIndex point)
  check past vector = do
    let Just env = vecEnv vector cmr
        tx = P.envTx env
        inputs = V.toList (D.sigTxIn tx)
        outputs = V.toList (D.sigTxOut tx)
        stateInput = head inputs
        statePoint = D.sigTxiPreviousOutpoint stateInput
        inputSum = sum (map (toInteger . D.sigTxiValue) inputs)
        outputSum = sum (map (toInteger . D.txoValue) outputs)
        link = case find ((== D.opHash statePoint) . D.txid) past of
          Nothing -> pointKey statePoint == pointKey (dummyOutpoint 500)
            && toInteger (D.sigTxiValue stateInput) == Ref.treasury
          Just parent -> let continued = D.sigTxOut parent V.! 0
                         in D.opIndex statePoint == 0 && D.txoValue continued == D.sigTxiValue stateInput
                            && D.txoScript continued == D.sigTxiScript stateInput
        wire = runPut (D.putNoWitnessTx tx)
    parsed <- either fail return (parseRawTx wire)
    let matchesWire = runPut (D.putNoWitnessTx (rawToSigTx parsed)) == wire
          && map (pointKey . riOutpoint) (rtIns parsed) == map (pointKey . D.sigTxiPreviousOutpoint) inputs
        inputBoundary (index, input) =
          let i = w32 index
              point = D.sigTxiPreviousOutpoint input
              raw = (w256FromBytes (hashToBytes (D.opHash point)), w32 (toInteger (D.opIndex point)))
              amount = w64 (toInteger (D.sigTxiValue input))
              scriptHash = w256FromBytes (hashToBytes (sha256 (BL.toStrict (D.sigTxiScript input))))
          in C.input_prev_outpoint env i == Just (Right raw) && P.primSem P.InputPrevOutpoint i env == Just (Right raw)
            && C.input_value env i == Just (Right amount) && P.primSem P.InputValue i env == Just (Right amount)
            && C.input_script_hash env i == Just (Right scriptHash) && P.primSem P.InputScriptHash i env == Just (Right scriptHash)
        outputBoundary (index, output) =
          let i = w32 index
              amount = w64 (toInteger (D.txoValue output))
              scriptHash = w256FromBytes (hashToBytes (sha256 (BL.toStrict (D.txoScript output))))
          in C.output_value env i == Just (Right amount) && P.primSem P.OutputValue i env == Just (Right amount)
            && C.output_script_hash env i == Just (Right scriptHash) && P.primSem P.OutputScriptHash i env == Just (Right scriptHash)
        feePoint = pointKey (D.sigTxiPreviousOutpoint (last inputs))
        usedFeePoints = map (pointKey . D.sigTxiPreviousOutpoint . V.last . D.sigTxIn) past
        expectedDistance = if D.sigTxiSequence stateInput == 0xfffffffe then 0 else toInteger (D.sigTxiSequence stateInput)
        distance = fromWord16 <$> C.tx_lock_distance env ()
        csv = distance == Just expectedDistance
          && (expectedDistance == 0 || C.check_lock_distance env (w16 expectedDistance) == Just ())
    assert ("actual raw wire, ancestry, C/Haskell primitives, CSV and fee for " ++ vecName vector)
      (matchesWire && link && inputSum - outputSum == Ref.fee && feePoint `notElem` usedFeePoints
       && C.current_index env () == Just (w32 0) && csv
       && all inputBoundary (zip [0..] inputs) && all outputBoundary (zip [0..] outputs))
    putStrLn ("positive txid_raw=" ++ hex (hashToBytes (D.txid tx)) ++ " outputs_sats=" ++ show (map D.txoValue outputs)
      ++ " relative_distance=" ++ show distance)
    return (tx : past)
