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
import Simplicity.Ty.Word (fromWord16, fromWord64)
import qualified JetDiscovery.Corpus.UmaBond as Uma
import JetDiscovery.Lib.Bytes (w16, w32, w64, w256FromBytes)
import qualified JetDiscovery.Ref.UmaBond as Ref
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
  checkFees
  case Uma.entry of
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
      assert "all 42 actual native vectors pass at one canonical CMR" (eligible && length vectors == 42 && and passed)
      checkWireChain cmr (filter ((== Accept) . vecExpect) vectors)

checkFees :: IO ()
checkFees = do
  let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 BL.empty 0xfffffffe] [mkOutput 999 (unhex "51")] 0)
        0 defaultTap (hashFromInteger 1)
      amounts = [2000..2031] ++ [23998..24003] ++ [999998..1000000]
      evaluator = J.unwrap (J.jetSubst Uma.bondFee)
      fee amount = fromWord64 <$> J.fastEval evaluator env (w64 amount)
  assert "native Store fee agrees with source Integer flooring at all 41 tested bonds"
    (length amounts == 41 && all (\amount -> fee amount == Just (Ref.storeFee amount)) amounts)
  assert "even 24000 and odd 24001 each pay 12000 to the Store"
    (fee 24000 == Just 12000 && fee 24001 == Just 12000)

checkWireChain :: Hash256 -> [Vector w] -> IO ()
checkWireChain cmr vectors = do
  previous <- foldM check [] vectors
  assert "all 11 positive raw-wire and linked fixtures checked" (length previous == 11)
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
        setupPoint = (hashFromInteger 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00, 77)
        link = case find ((== D.opHash statePoint) . D.txid) past of
          Nothing -> pointKey statePoint == setupPoint && toInteger (D.sigTxiValue stateInput) == Ref.carrier
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
        relativeDistance = fromWord16 <$> C.tx_lock_distance env ()
        expectedDistance = if D.sigTxiSequence stateInput == 10 then 10 else 0
        csv = relativeDistance == Just expectedDistance
          && (length outputs /= 2 || C.check_lock_distance env (w16 Ref.delay) == Just ())
    assert ("actual raw wire, ancestry, C/Haskell primitives, CSV and fee for " ++ vecName vector)
      (matchesWire && link && inputSum - outputSum == Ref.fee && feePoint `notElem` usedFeePoints
       && C.current_index env () == Just (w32 0) && csv
       && all inputBoundary (zip [0..] inputs) && all outputBoundary (zip [0..] outputs))
    putStrLn ("positive txid_raw=" ++ hex (hashToBytes (D.txid tx)) ++ " outputs_sats=" ++ show (map D.txoValue outputs)
      ++ " relative_distance=" ++ show relativeDistance)
    return (tx : past)
