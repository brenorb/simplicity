-- | Serialize EIP-197 pairing programs (monomorphic Bn254PairingDag) for bench/run_program.
--
--   bn254-pairing-dag-dump units DIR            component checks against the Integer reference
--   bn254-pairing-dag-dump vectors DIR [NAME..]  go-ethereum vectors, each with a flipped-output twin
--
-- Each unit program is witness (inputs, expected) >>> (op inputs == expected) >>> verify,
-- written once with the reference result (must run OK) and once with a wrong
-- expected value (must fail).  Costs come from libsimplicity's static analysis
-- in run_program, which reproduces the Haskell cost bounds exactly on the
-- EIP-196 programs.
module Main where
import Control.Monad (forM_)
import qualified Data.ByteString as BS
import Data.Bits (setBit)
import Data.List (foldl')
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
import Prelude hiding (take, drop)
import Simplicity.Term.Core
import qualified Prelude as P
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Bit (verify)
import Simplicity.Ty
import qualified Simplicity.Bitcoin.Dag as Dag
import qualified Simplicity.Bitcoin.Serialization.BitString as Bits
import qualified Simplicity.Bitcoin.Inference as I
import JetDiscovery.Cost (TermWeight, milliWeigh)
import qualified JetDiscovery.Followup.Bn254PairingRef as R
import JetDiscovery.Followup.Bn254PairingDag

pack :: [Bool] -> BS.ByteString
pack [] = BS.empty
pack bs = let (h, t) = splitAt 8 bs
          in BS.cons (foldl' (\acc (i, b) -> if b then setBit acc (7 - i) else acc) 0 (zip [0 ..] h)) (pack t)

dumpDag :: FilePath -> T () () -> IO ()
dumpDag prefix t = do
  let dag = Dag.jetDag t
      -- exact static bound (milliWU, unbounded) from the same DAG, via the corpus cost algebra
      cost = either (error . ("cost type check: " ++)) milliWeigh (I.typeCheck dag :: Either String (TermWeight () ()))
  writeFile (prefix ++ ".cost.txt") (show cost ++ "\n")
  BS.writeFile (prefix ++ ".program.bin") (pack (Bits.putDagNoWitnessLengthCode dag))
  BS.writeFile (prefix ++ ".witness.bin") (pack (maybe (error "witness") id (Bits.putWitnessData dag)))
  putStrLn ("dumped " ++ prefix ++ " cost_mwu=" ++ show cost) >> hFlush stdout

-- | (op inputs == expected) for a witness pair (inputs, expected).
check :: (TyC a, TyC b) => T a b -> a -> b -> T () ()
check op x e = witness (x, e) >>> (((oh >>> op) &&& ih) >>> eq >>> verify)

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of (a, []) -> [a]; (a, _:rest) -> a : splitOn c rest

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = P.take n xs : chunk n (P.drop n xs)

sample :: Integer -> R.F12
sample k = ((g 1, g 2, g 3), (g 4, g 5, g 6))
 where g i = ((k * 7919 * i * i + 13 * i + k) `mod` R.p, (k * 104729 * i + 3 * i * i * i + 1) `mod` R.p)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["units", dir] -> do
      let a = sample 1
          b = sample 2
          bad e = R.f12mul e (sample 5)
          units = [ ("f12mul", \e -> check f12mulT (montyF12 a, montyF12 b) (montyF12 e), R.f12mul a b)
                  , ("f12sq", \e -> check f12sqT (montyF12 a) (montyF12 e), R.f12sq a)
                  , ("frob", \e -> check frobT (montyF12 a) (montyF12 e), R.frob a)
                  , ("powu", \e -> check powUT (montyF12 a) (montyF12 e), R.f12pow a R.u)
                  , ("finalexp", \e -> check (finalExpT (montyF12 (R.f12inv a))) (montyF12 a) (montyF12 e), R.finalExpDirect a) ]
      forM_ units $ \(n, mk, e) -> do
        dumpDag (dir ++ "/unit-" ++ n) (mk e)
        dumpDag (dir ++ "/unit-" ++ n ++ "-wrong") (mk (bad e))
    "vectors" : dir : names -> do
      rows <- map (splitOn '\t') . P.drop 1 . lines <$> readFile "reports/data/followup-bn254-pairing-vectors.tsv"
      let vecs = [ (n, [ ((x1, y1), (c, d, x, y)) | [x1, y1, c, d, x, y] <- chunk 6 ws' ], read ("0x" ++ e))
                 | ["pairing", n, ws, e] <- rows, null names || n `elem` names
                 , let ws' = if ws == "-" then [] else map (\h -> read ("0x" ++ h)) (splitOn ',' ws) ]
      forM_ vecs $ \(n, raw, out) -> do
        dumpDag (dir ++ "/" ++ n) (pairingT (pairingHints raw out))
        dumpDag (dir ++ "/" ++ n ++ "-flipped") (pairingT (pairingHints raw (1 - out)))
    _ -> putStrLn "usage: units DIR | vectors DIR [NAME...]"
