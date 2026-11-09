-- | Check and measure followup/src/JetDiscovery/Followup/FrostTranscript.hs.
--
--   ghc -O1 -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
--       -ifollowup/src tools/FrostTranscriptSmoke.hs
--
-- 1. The Integer reference reproduces RFC 9591 E.5's published binding factors,
--    group commitment and aggregate signature.
-- 2. Every vector gives its expected outcome (per-vector CMR check).
-- 3. The static cost bound with existing jets and with candidate overlays.
module Main where
import Control.Monad (forM_, unless)
import qualified Data.ByteString as BS
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import JetDiscovery.Types
import JetDiscovery.Run
import qualified JetDiscovery.Ref.Bip340 as Ref
import JetDiscovery.Followup.FrostTranscript

main :: IO ()
main = do
  let (msg, cs, zs) = rfcVector
      (rhos, rEnc, z) = rfcExpected
      Just pk = Just (pkOf cs)
      pkOf _ = groupKey
      groupKey = case Ref.liftX 0xf37c34b66ced1fb51c34a90bdae006901f10625cc06c4f64663b0eae87d87b4f of
                   Just q -> q
                   Nothing -> error "group key"
      gotRhos = map snd (refBindingFactors pk msg cs)
      Just r = refGroupCommitment pk msg cs
      enc (x, y) = BS.cons (if even y then 2 else 3) (Ref.bytesFromInt x)
      zSum = sum zs `mod` Ref.n
      c = refChallenge r pk msg
      aggOk = Ref.pointMul Ref.gPt zSum == Ref.pointAdd (Just r) (Ref.pointMul (Just pk) c)
  say ("reference binding factors match RFC: " ++ show (gotRhos == rhos))
  say ("reference group commitment matches RFC: " ++ show (enc r == rEnc))
  say ("sum of RFC shares equals RFC z: " ++ show (zSum == z))
  say ("reference aggregate equation holds: " ++ show aggOk)
  unless (gotRhos == rhos && enc r == rEnc && zSum == z && aggOk) exitFailure
  case entry of
    Entry ident _ _ _ _ _ make vectors -> do
      let first = make (vecWitness (head vectors))
          cmr = progCmr first
      say (ident ++ " CMR=" ++ show cmr)
      results <- mapM (\res -> do
          say (vrName res ++ "\texpected=" ++ show (vrExpect res) ++ "\t" ++ vrNote res ++ "\tpass=" ++ show (vrOk res))
          return (vrOk res)) (runVectors make cmr vectors)
      unless (and results) exitFailure
      say ("vectors: " ++ show (length results) ++ "/" ++ show (length results) ++ " pass")
      let m = measure first
      say ("cost_mwu=" ++ show (mCost m) ++ " primitive_mwu=" ++ show (mCostBase m) ++ " whatif_mwu=" ++ show (mCostWhatIf m))
      say ("program_bits=" ++ show (mProgBits m) ++ " witness_bits=" ++ show (mWitBits m) ++ " dag_nodes=" ++ show (mNodes m))
      say ("budget_max_fraction=" ++ show (fromIntegral (mCost m) / 1000 / fromIntegral budgetMax :: Double))
      forM_ (mCandidateCosts m) $ \(name, (iso, occ, sites)) ->
        unless (sites == 0) $ say ("candidate " ++ name ++ " isolated_mwu=" ++ show iso ++ " occurrences=" ++ show occ ++ " sites=" ++ show sites)
      forM_ (mAblations m) $ \(name, cost) -> say ("ablation " ++ name ++ " mwu=" ++ show cost)
 where say s = putStrLn s >> hFlush stdout
