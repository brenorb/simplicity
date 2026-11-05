{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -O0 #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM, forM_, unless)
import qualified Data.ByteString.Lazy as BL
import Data.List (find)
import Data.Serialize (runPut)
import qualified Data.Vector as V
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.FFI.Jets as C
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import Simplicity.Digest (Hash256)
import Simplicity.Ty.Word (fromWord64)
import qualified JetDiscovery.Corpus.SablierStream as Stream
import JetDiscovery.Lib.Bytes (w32, w64, w256FromBytes)
import qualified JetDiscovery.Ref.SablierStream as Ref
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
  checkArithmetic
  case Stream.entry of
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
      assert "all 38 full native vectors pass at one canonical CMR" (eligible && length vectors == 38 && and passed)
      checkWireChain cmr (filter ((== Accept) . vecExpect) vectors)

checkArithmetic :: IO ()
checkArithmetic = do
  let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 BL.empty 0xfffffffe] [mkOutput 999 (unhex "51")] 0)
        0 defaultTap (hashFromInteger 1)
      evaluator = J.unwrap (J.jetSubst Stream.streamedAt)
      evaluateHeight height = fromWord64 <$> J.fastEval evaluator env (w32 height)
      heights = [0] ++ [Ref.startHeight - 3 .. Ref.endHeight + 3] ++ [Ref.heightLimit - 1]
      explicit = [(799999,0),(800000,2500),(800010,2500),(800011,7100),(800017,7100),(800018,12486),
        (800024,12486),(800025,17873),(800032,23259),(800039,28646),(800046,34032),(800049,34032),(800050,37111)]
  forM_ explicit $ \(height, amount) ->
    assert ("literal vesting boundary " ++ show height ++ " gives " ++ show amount) (evaluateHeight height == Just amount)
  assert ("actual native arithmetic equals Integer source formula at all " ++ show (length heights) ++ " heights")
    (all (\height -> evaluateHeight height == Just (Ref.streamedAt height)) heights)

checkWireChain :: Hash256 -> [Vector w] -> IO ()
checkWireChain cmr vectors = do
  previous <- foldM check [] vectors
  assert "all 13 positive linked transaction fixtures checked" (length previous == 13)
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
          Nothing -> null past && pointKey statePoint == pointKey (dummyOutpoint 100)
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
        feePoint = pointKey (D.sigTxiPreviousOutpoint (inputs !! 1))
        usedFeePoints = map (pointKey . D.sigTxiPreviousOutpoint . (V.! 1) . D.sigTxIn) past
    assert ("actual raw wire, ancestry, C/Haskell primitives and 1000-sat fee for " ++ vecName vector)
      (matchesWire && link && inputSum - outputSum == Ref.fee && feePoint `notElem` usedFeePoints
       && C.current_index env () == Just (w32 0) && C.lock_time env () == Just (w32 (toInteger (D.sigTxLock tx)))
       && all inputBoundary (zip [0..] inputs) && all outputBoundary (zip [0..] outputs))
    putStrLn ("positive txid_raw=" ++ hex (hashToBytes (D.txid tx)) ++ " outputs_sats=" ++ show (map D.txoValue outputs))
    return (tx : past)
