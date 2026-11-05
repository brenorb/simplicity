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
import Simplicity.Ty.Word (fromWord32)
import qualified JetDiscovery.Corpus.Clipper as Clipper
import JetDiscovery.Lib.Bytes (w32, w64, w256FromBytes)
import qualified JetDiscovery.Ref.Clipper as Ref
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
  case Clipper.entry of
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
      assert "all 51 actual Clipper vectors pass at one canonical CMR" (eligible && length vectors == 51 && and passed)
      checkWireChain cmr (filter ((== Accept) . vecExpect) vectors)

checkArithmetic :: IO ()
checkArithmetic = do
  let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 BL.empty 0xfffffffe] [mkOutput 999 (unhex "51")] 0)
        0 defaultTap (hashFromInteger 1)
      elapsed = [0..110] ++ [Ref.eventLimit]
      priceEvaluator = J.unwrap (J.jetSubst Clipper.price)
      fillEvaluator = J.unwrap (J.jetSubst Clipper.takeFill)
      evaluatePrice duration = fromWord32 <$> J.fastEval priceEvaluator env (w32 duration)
      evaluateFill (lot, debt, request, duration) =
        let input = (w32 lot, (w32 debt, (w32 request, w32 (Ref.priceRaw duration `div` Ref.ray))))
        in (\(slice, owe) -> (fromWord32 slice, fromWord32 owe)) <$> J.fastEval fillEvaluator env input
      expectedFill (lot, debt, request, duration) = Ref.fill lot debt request duration
      literal = [(120,8301,30,10),(90,5601,60,20),(33,1000,20,25),(33,1000,1,25),
                 (10,1000,10,20),(30,1600,20,20),(10,50,5,0),(80,5201,10,1)]
      grid = [(lot,debt,request,duration) | lot <- [1,10,90], debt <- [50,1000,1801,5601],
               request <- [0,1,10,60,150], duration <- [0,20,60,100]]
  assert "native curve agrees with the full source RAY result at all 112 elapsed inputs"
    (length elapsed == 112 && all (\duration -> evaluatePrice duration == Just (Ref.priceRaw duration `div` Ref.ray)) elapsed)
  assert "native fill agrees with the full source RAY result at all 248 bounded fill inputs"
    (length (literal ++ grid) == 248 && all (\input -> evaluateFill input == expectedFill input) (literal ++ grid))
  assert "dust keeps exact 4601 owed and floors the collateral slice to 57"
    (evaluateFill (90,5601,60,20) == Just (57,4601))
  assert "cap keeps exact 1000 owed and floors the collateral slice to 13"
    (evaluateFill (33,1000,20,25) == Just (13,1000))

checkWireChain :: Hash256 -> [Vector w] -> IO ()
checkWireChain cmr vectors = do
  previous <- foldM check [] vectors
  assert "all 16 positive raw-wire and linked fixtures checked" (length previous == 16)
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
        setupPoint = pointKey (dummyOutpoint 555)
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
    assert ("actual raw wire, ancestry, C/Haskell primitives and fee for " ++ vecName vector)
      (matchesWire && link && inputSum - outputSum == Ref.fee && feePoint `notElem` usedFeePoints
       && C.current_index env () == Just (w32 0) && C.lock_time env () == Just (w32 0)
       && all inputBoundary (zip [0..] inputs) && all outputBoundary (zip [0..] outputs))
    putStrLn ("positive txid_raw=" ++ hex (hashToBytes (D.txid tx)) ++ " outputs_sats=" ++ show (map D.txoValue outputs) )
    return (tx : past)
