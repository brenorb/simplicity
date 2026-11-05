{-# OPTIONS_GHC -O0 #-}
module Main where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import qualified Simplicity.Bitcoin.Jets as J
import qualified JetDiscovery.Corpus.Bip347Cat as Cat
import qualified JetDiscovery.Ref.OpCat as Ref
import JetDiscovery.Report (vectorsOk)
import JetDiscovery.Run
import JetDiscovery.Types
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdout)

assert :: String -> Bool -> IO ()
assert label result = do
  putStrLn (label ++ "=" ++ show result)
  unless result exitFailure

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  e@(Entry ident _ _ _ _ _ make vectors) <- Cat.entry
  let first = head vectors
      eligible = case boundView (make (vecWitness first)) of
        Just (BoundView kernel _) -> boundEligible kernel
        Nothing -> False
  assert "single typed witness and prepared closed kernel" eligible
  result <- runEntryIO e
  let m = erMeasure result
      count ex = length (filter ((== ex) . vrExpect) (erVectors result))
      accepted = count Accept
      rejected = count Reject
  putStrLn (ident ++ " CMR=" ++ show (mCmr m)
    ++ " native_mwu=" ++ show (mCost m)
    ++ " primitive_only_mwu=" ++ show (mCostBase m)
    ++ " overlay_estimate_mwu=" ++ show (mCostWhatIf m)
    ++ " program_bits=" ++ show (mProgBits m)
    ++ " witness_bits=" ++ show (mWitBits m)
    ++ " nodes=" ++ show (mNodes m)
    ++ " accepts=" ++ show accepted
    ++ " rejects=" ++ show rejected)
  assert "all 342 same-CMR CAT claim vectors and analysis checks passed"
    (accepted + rejected == 342 && vectorsOk result)
  let Just env = vecEnv first (mCmr m)
      evaluate = J.fastEval (J.unwrap (J.jetSubst Cat.catValue)) env
      left size = BS.pack [fromIntegral (i * 53 + 17) | i <- [0..size-1]]
      right size = BS.pack [fromIntegral (i * 29 + 233) | i <- [0..size-1]]
      compareSplit l r =
        let a = left l
            b = right r
            actual = evaluate (Cat.encode a, Cat.encode b)
        in case (Ref.cat a b, actual) of
             (Just expected, Just element) -> Cat.decode element == Just expected
             (Nothing, Nothing) -> True
             _ -> False
  assert "all 521 splits summing to 520 produce the reference bytes"
    (and [compareSplit l (520-l) | l <- [0..520]])
  assert "all 520 valid-input splits summing to 521 fail"
    (and [compareSplit l (521-l) | l <- [1..520]])
