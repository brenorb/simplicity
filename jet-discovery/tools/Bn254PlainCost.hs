-- | What-if: the EIP-196 relations with the field multiply replaced by the
-- bn254_fp_multiply candidate's specification (tools/gen_bn254_plain.sh).
-- Static cost with existing jets and with the candidate overlay; ECADD vectors
-- are also run to confirm the variant is the same relation.
module Main where
import Control.Monad (forM_, unless)
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import Simplicity.Term.Core (witness, (>>>))
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx
import JetDiscovery.Followup.Bn254PrecompilesPlain

hexI :: String -> Integer
hexI s = read ("0x" ++ s)

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of (a, []) -> [a]; (a, _:rest) -> a : splitOn c rest

main :: IO ()
main = do
  rows <- map (splitOn '\t') . drop 1 . lines <$> readFile "reports/data/followup-bn254-vectors.tsv"
  let env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
      adds = [ Vector ("geth " ++ n) env (addWitness (a, b) (c, d) (e, f)) Accept | ["add", n, ws, outs] <- rows
             , let [a, b, c, d] = map hexI (splitOn ',' ws), let [e, f] = map hexI (splitOn ',' outs) ]
      report name prog = do
        let m = measure prog
        say (name ++ " cost_mwu=" ++ show (mCost m) ++ " whatif_mwu=" ++ show (mCostWhatIf m))
        forM_ (mCandidateCosts m) $ \(c, (iso, occ, sites)) ->
          unless (sites == 0) $ say (name ++ " candidate " ++ c ++ " isolated_mwu=" ++ show iso ++ " occurrences=" ++ show occ)
  case adds of
    v : _ -> report "plain-ecadd" (Prog (witness (vecWitness v) >>> ecaddT))
    [] -> exitFailure
  report "plain-ecmul" (Prog (witness (mulWitness (1, 2) 5 (0, 0)) >>> ecmulT))
  let make w = Prog (witness w >>> ecaddT)
      cmr = progCmr (make (vecWitness (head adds)))
  ok <- mapM (\r -> say ("plain-ecadd\t" ++ vrName r ++ "\tpass=" ++ show (vrOk r)) >> return (vrOk r)) (runVectors make cmr adds)
  say ("plain-ecadd vectors: " ++ show (length (filter id ok)) ++ "/" ++ show (length ok))
  unless (and ok) exitFailure
 where say s = putStrLn s >> hFlush stdout
