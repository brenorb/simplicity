{-# LANGUAGE RankNTypes #-}
-- | Check and measure followup/src/JetDiscovery/Followup/Bn254Pairing.hs.
--
--   bn254-pairing-smoke units            component terms against the Integer reference
--   bn254-pairing-smoke cost K           static cost of the K-pair program
--   bn254-pairing-smoke vectors NAME...  run the named go-ethereum vectors (with CMR checks)
module Main where
import Control.Monad (forM, forM_, unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, stdout)
import Simplicity.Term.Core (witness, (>>>))
import Simplicity.Ty
import Simplicity.Ty.Word (toWord256)
import Simplicity.Digest (Hash256)
import qualified Simplicity.Bitcoin.Term as BT
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Primitive (PrimEnv)
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx
import qualified JetDiscovery.Followup.Bn254PairingRef as R
import JetDiscovery.Followup.Bn254Pairing
import JetDiscovery.Followup.Dump (dumpProg)

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of (a, []) -> [a]; (a, _:rest) -> a : splitOn c rest

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = take n xs : chunk n (drop n xs)

envT :: Hash256 -> Maybe PrimEnv
envT = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap

env0 :: PrimEnv
env0 = maybe (error "env") id (envT (hashFromInteger 0))

say :: String -> IO ()
say s = putStrLn s >> hFlush stdout

evalT :: (TyC a, TyC b) => (forall term. BT.Simplicity term => term a b) -> a -> Maybe b
evalT t = J.fastEval (J.unwrap (J.jetSubst t)) env0

-- Deterministic Fp12 test values.
sample :: Integer -> R.F12
sample k = ((g 1, g 2, g 3), (g 4, g 5, g 6))
 where g i = ((k * 7919 * i * i + 13 * i + k) `mod` R.p, (k * 104729 * i + 3 * i * i * i + 1) `mod` R.p)

units :: IO Bool
units = do
  let xs = map sample [1, 2, 3]
      pairsOf = zip xs (drop 1 xs ++ take 1 xs)
      c2 ((a, _, _), _) = a
      c6 (a, _) = a
      chk name ok = say ("unit " ++ name ++ ": " ++ (if ok then "PASS" else "FAIL")) >> return ok
  r1 <- forM pairsOf $ \(a, b) -> chk "f2mul" (evalT f2mulT (montyF2' (c2 a), montyF2' (c2 b)) == Just (montyF2' (R.f2mul (c2 a) (c2 b))))
  r2 <- forM pairsOf $ \(a, b) -> chk "f6mul" (evalT f6mulT (m6' (c6 a), m6' (c6 b)) == Just (m6' (R.f6mul (c6 a) (c6 b))))
  r3 <- forM pairsOf $ \(a, b) -> chk "f12mul" (evalT f12mulT (montyF12 a, montyF12 b) == Just (montyF12 (R.f12mul a b)))
  r4 <- forM xs $ \a -> chk "f12sq" (evalT f12sqT (montyF12 a) == Just (montyF12 (R.f12sq a)))
  r5 <- forM xs $ \a -> chk "frob" (evalT frobT (montyF12 a) == Just (montyF12 (R.frob a)))
  r6 <- forM xs $ \a -> chk "conj12" (evalT conj12T (montyF12 a) == Just (montyF12 (R.f12conj a)))
  r7 <- forM (take 1 xs) $ \a -> chk "powU" (evalT powUT (montyF12 a) == Just (montyF12 (R.f12pow a R.u)))
  return (and (concat [r1, r2, r3, r4, r5, r6, r7]))
 where
  montyF2' (a, b) = (toWord256 (monty a), toWord256 (monty b))
  m6' (a, b, c) = (montyF2' a, (montyF2' b, montyF2' c))

loadVectors :: IO [(String, [((Integer, Integer), (Integer, Integer, Integer, Integer))], Integer)]
loadVectors = do
  rows <- map (splitOn '\t') . drop 1 . lines <$> readFile "reports/data/followup-bn254-pairing-vectors.tsv"
  return [ (n, [ ((a, b), (c, d, x, y)) | [a, b, c, d, x, y] <- chunk 6 ws' ], read ("0x" ++ e))
         | ["pairing", n, ws, e] <- rows
         , let ws' = if ws == "-" then [] else map (\h -> read ("0x" ++ h)) (splitOn ',' ws) ]

progOf :: PairingW -> Prog
progOf w = Prog (pairingT w)

main :: IO ()
main = do
  args <- getArgs
  vecs <- loadVectors
  case args of
    ["units"] -> do ok <- units; unless ok exitFailure; say "all unit checks pass"
    ["cost", k] -> do
      let (_, raw, out) = head [ v | v@(_, ps, _) <- vecs, length ps == read k ]
          m = measure (progOf (pairingHints raw out))
      say ("pairs=" ++ k ++ " cost_mwu=" ++ show (mCost m) ++ " program_bits=" ++ show (mProgBits m) ++ " witness_bits=" ++ show (mWitBits m) ++ " dag_nodes=" ++ show (mNodes m))
      forM_ (mCandidateCosts m) $ \(name, (iso, occ, sites)) ->
        unless (sites == 0) $ say ("pairs=" ++ k ++ " candidate " ++ name ++ " isolated_mwu=" ++ show iso ++ " occurrences=" ++ show occ)
    "vectors" : names -> do
      oks <- forM [ v | v@(n, _, _) <- vecs, n `elem` names ] $ \(n, raw, out) -> do
        let good = Vector ("geth " ++ n) envT (pairingHints raw out) Accept
            -- the opposite claimed output must reject
            bad = Vector ("geth " ++ n ++ " with flipped output") envT (pairingHints raw (1 - out)) Reject
            cmr = progCmr (progOf (pairingHints raw out))
        say (n ++ " pairs=" ++ show (length raw) ++ " CMR=" ++ show cmr)
        rs <- forM (runVectors progOf cmr [good, bad]) $ \r -> do
          say (n ++ "\t" ++ vrName r ++ "\texpected=" ++ show (vrExpect r) ++ "\t" ++ vrNote r ++ "\tpass=" ++ show (vrOk r))
          return (vrOk r)
        return (and rs)
      unless (and oks) exitFailure
      say ("vectors: " ++ show (length (filter id oks)) ++ "/" ++ show (length oks) ++ " pass")
    "dump" : dir : names -> forM_ [ v | v@(n, _, _) <- vecs, null names || n `elem` names ] $ \(n, raw, out) -> do
      dumpProg (dir ++ "/" ++ n) (progOf (pairingHints raw out))
      dumpProg (dir ++ "/" ++ n ++ "-flipped") (progOf (pairingHints raw (1 - out)))
      say ("dumped " ++ n ++ " pairs=" ++ show (length raw))
    _ -> say "usage: units | cost K | vectors NAME... | dump DIR [NAME...]"
