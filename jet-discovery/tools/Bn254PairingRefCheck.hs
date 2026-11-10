-- | Check the Integer pairing reference against go-ethereum's EIP-197 vectors.
module Main where
import Control.Monad (forM, unless)
import System.Exit (exitFailure)
import JetDiscovery.Followup.Bn254PairingRef

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of (a, []) -> [a]; (a, _:rest) -> a : splitOn c rest

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = take n xs : chunk n (drop n xs)

main :: IO ()
main = do
  putStrLn ("selfCheck (inverse, Frobenius p and p^2, hard part == direct exponentiation): " ++ show selfCheck)
  rows <- map (splitOn '\t') . drop 1 . lines <$> readFile "reports/data/followup-bn254-pairing-vectors.tsv"
  oks <- forM [ (n, w, e) | ["pairing", n, w, e] <- rows ] $ \(n, ws, e) -> do
    let words' = if ws == "-" then [] else map (\h -> read ("0x" ++ h)) (splitOn ',' ws)
        pairs = [ ((a, b), (c, d, x, y)) | [a, b, c, d, x, y] <- chunk 6 words' ]
        want = Just (read ("0x" ++ e) == (1 :: Integer))
        got = pairingCheck pairs
    putStrLn (n ++ "\tpairs=" ++ show (length pairs) ++ "\texpected=" ++ show want ++ "\tgot=" ++ show got ++ "\t" ++ (if got == want then "PASS" else "FAIL"))
    return (got == want)
  unless (selfCheck && and oks) exitFailure
  putStrLn ("all " ++ show (length oks) ++ " vectors pass")
