-- | Check and measure followup/src/JetDiscovery/Followup/Bn254Precompiles.hs.
--
--   ghc -O1 -rtsopts -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
--       -ifollowup/src tools/Bn254PrecompileSmoke.hs
--
-- 1. The Integer reference reproduces every go-ethereum expected output.
-- 2. Every vector (go-ethereum successes plus derived failures and wrong
--    claimed outputs) gives its expected outcome with a per-vector CMR check.
-- 3. Static cost bounds with existing jets.
module Main where
import Control.Monad (forM_, unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import Simplicity.Term.Core (witness, (>>>))
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx
import JetDiscovery.Followup.Bn254Precompiles

hexI :: String -> Integer
hexI s = read ("0x" ++ s)

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of (a, []) -> [a]; (a, _:rest) -> a : splitOn c rest

main :: IO ()
main = do
  allArgs <- getArgs
  -- optional trailing "--vectors FROM TO": run only vectors [FROM, TO) and skip the cost measurement
  let (args, range) = case break (== "--vectors") allArgs of
        (a, ["--vectors", from, to]) -> (a, Just (read from :: Int, read to :: Int))
        (a, _) -> (a, Nothing)
  rows <- map (splitOn '\t') . tail . lines <$> readFile "reports/data/followup-bn254-vectors.tsv"
  let env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
      adds = [ (n, (a, b), (c, d), (e, f)) | ["add", n, ws, outs] <- rows
             , let [a, b, c, d] = map hexI (splitOn ',' ws), let [e, f] = map hexI (splitOn ',' outs) ]
      muls = [ (n, (a, b), s, (e, f)) | ["mul", n, ws, outs] <- rows
             , let [a, b, s] = map hexI (splitOn ',' ws), let [e, f] = map hexI (splitOn ',' outs) ]
      refOk = and [ refAdd p q == Just o | (_, p, q, o) <- adds ] && and [ refMul p s == Just o | (_, p, s, o) <- muls ]
  say ("Integer reference reproduces all " ++ show (length adds + length muls) ++ " go-ethereum outputs: " ++ show refOk)
  unless refOk exitFailure
  let g = (1, 2)
      offCurve = (1, 3)
      bump (x, y) = (x, (y + 1) `mod` pBN)
      addVecs = [ Vector ("geth " ++ n) env (addWitness p q o) Accept | (n, p, q, o) <- adds ]
             ++ [ Vector "first coordinate equals p" env (addWitness (pBN, 2) g g) Reject
                , Vector "second point off the curve" env (addWitness g offCurve g) Reject
                , Vector "wrong claimed sum" env (addWitness g g (bump (maybe (0, 0) id (refAdd g g)))) Reject
                , Vector "claimed infinity for G + G" env (addWitness g g (0, 0)) Reject ]
      mulVecs = [ Vector ("geth " ++ n) env (mulWitness p s o) Accept | (n, p, s, o) <- muls ]
             ++ [ Vector "point off the curve" env (mulWitness offCurve 5 (0, 0)) Reject
                , Vector "y equals p" env (mulWitness (1, pBN) 5 (0, 0)) Reject
                , Vector "wrong claimed product" env (mulWitness g 5 (bump (maybe (0, 0) id (refMul g 5)))) Reject ]
      addEntry = Entry "followup-eip196-bn254-ecadd" "EIP-196 BN254 G1 addition precompile relation"
                   "EIP-196 0x06 ECADD" CrossChain (Upstream "vendor-specs-followup/bn254/bn256Add.json plus derived failures")
                   [] (\w -> Prog (witness w >>> ecaddT)) addVecs
      mulEntry = Entry "followup-eip196-bn254-ecmul" "EIP-196 BN254 G1 scalar multiplication precompile relation"
                   "EIP-196 0x07 ECMUL" CrossChain (Upstream "vendor-specs-followup/bn254/bn256ScalarMul.json plus derived failures")
                   [] (\w -> Prog (witness w >>> ecmulT)) mulVecs
  forM_ [ e | e@(Entry i _ _ _ _ _ _ _) <- [addEntry, mulEntry], null args || i `elem` args ] $ \(Entry ident _ _ _ _ _ make vectors) -> do
    let first = make (vecWitness (head vectors))
        cmr = progCmr first
        m = measure first
        chosen = maybe vectors (\(a, b) -> take (b - a) (drop a vectors)) range
    say (ident ++ " CMR=" ++ show cmr)
    unless (range /= Nothing) $ do
      say (ident ++ " cost_mwu=" ++ show (mCost m) ++ " program_bits=" ++ show (mProgBits m) ++ " witness_bits=" ++ show (mWitBits m) ++ " dag_nodes=" ++ show (mNodes m))
      forM_ (mCandidateCosts m) $ \(name, (iso, occ, sites)) ->
        unless (sites == 0) $ say (ident ++ " candidate " ++ name ++ " isolated_mwu=" ++ show iso ++ " occurrences=" ++ show occ)
    results <- mapM (\r -> do
        say (ident ++ "\t" ++ vrName r ++ "\texpected=" ++ show (vrExpect r) ++ "\t" ++ vrNote r ++ "\tpass=" ++ show (vrOk r))
        return (vrOk r)) (runVectors make cmr chosen)
    say (ident ++ " vectors: " ++ show (length (filter id results)) ++ "/" ++ show (length results) ++ " pass")
    unless (and results) exitFailure
 where say s = putStrLn s >> hFlush stdout
