-- Standalone RFC 7693 F check for the registered fixed-final BLAKE2b arrow.
-- The reference uses ordinary Word64 arithmetic and an indexed state array.
module Main where

import Control.Monad (forM, unless)
import Data.Array (Array, (!), (//), listArray)
import Data.Bits (complement, rotateR, shiftR, xor)
import Data.List (foldl')
import Data.Word (Word64)
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdout)
import Text.Printf (printf)
import qualified JetDiscovery.Corpus.Hashes as Hashes
import JetDiscovery.Tx (defaultTap, dummyOutpoint, mkEnv, mkInput, mkOutput, mkTx)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Digest (hash0)
import qualified Simplicity.Ty.Word as W

type State = Array Int Word64
type Counter = (Word64, Word64)
type Input = ((W.Vector8 W.Word64, W.Vector16 W.Word64), (W.Word64, W.Word64))
type Output = W.Vector8 W.Word64

data Case = Case String [Word64] [Word64] Counter

iv :: [Word64]
iv =
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
  , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
  ]

-- RFC 7693 section 2.7. Rounds 10 and 11 repeat rows zero and one.
sigma :: [[Int]]
sigma =
  [ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
  , [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3]
  , [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4]
  , [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8]
  , [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13]
  , [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9]
  , [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11]
  , [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10]
  , [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5]
  , [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]
  ]

mix :: State -> ((Int, Int, Int, Int), (Word64, Word64)) -> State
mix v ((a,b,c,d),(x,y)) = v // [(a,a2), (b,b2), (c,c2), (d,d2)]
 where
  a1 = v!a + v!b + x
  d1 = rotateR (v!d `xor` a1) 32
  c1 = v!c + d1
  b1 = rotateR (v!b `xor` c1) 24
  a2 = a1 + b1 + y
  d2 = rotateR (d1 `xor` a2) 16
  c2 = c1 + d2
  b2 = rotateR (b1 `xor` c2) 63

compressReference :: [Word64] -> [Word64] -> Counter -> Bool -> [Word64]
compressReference h m (lo,hi) finalBlock =
  [word `xor` finished!i `xor` finished!(i+8) | (i,word) <- zip [0..7] h]
 where
  message = listArray (0,15) m :: State
  start = listArray (0,15) (h ++ iv) //
    [(12, (iv!!4) `xor` lo), (13, (iv!!5) `xor` hi),
     (14, if finalBlock then complement (iv!!6) else iv!!6)]
  lanes = [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
           (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]
  pairs (a:b:rest) = (message!a,message!b) : pairs rest
  pairs [] = []
  pairs _ = error "RFC message schedule has an odd size"
  oneRound v schedule = foldl' mix v (zip lanes (pairs schedule))
  finished = foldl' oneRound start (take 12 (cycle sigma))

pack8 :: [Word64] -> W.Vector8 W.Word64
pack8 xs = case map (W.toWord64 . toInteger) xs of
  [a,b,c,d,e,f,g,h] -> (((a,b),(c,d)),((e,f),(g,h)))
  _ -> error "expected eight input words"

pack :: [Word64] -> [Word64] -> Counter -> Input
pack h m (lo,hi) =
  ((pack8 h, (pack8 (take 8 m), pack8 (drop 8 m))),
   (W.toWord64 (toInteger lo), W.toWord64 (toInteger hi)))

unpack :: Output -> [Word64]
unpack (((a,b),(c,d)),((e,f),(g,h))) =
  map (fromInteger . W.fromWord64) [a,b,c,d,e,f,g,h]

rawCandidate :: J.FastEval J.JetType Input Output
rawCandidate = Hashes.blake2F Hashes.blake2b

jettedCandidate :: J.FastEval J.JetType Input Output
jettedCandidate = J.unwrap (J.jetSubst (Hashes.blake2F Hashes.blake2b))
{-# NOINLINE jettedCandidate #-}

abcState, abcBlock, abcAnswer :: [Word64]
abcState = case iv of
  h:rest -> (h `xor` 0x01010040) : rest
  [] -> error "BLAKE2b IV"
abcBlock = 0x00636261 : replicate 15 0
abcAnswer =
  [ 0x0d4d1c983fa580ba, 0xe9f6129fb697276a, 0xb7c45a68142f214c, 0xd1a2ffdb6fbb124b
  , 0x2d79ab2a39c5877d, 0x95cc3345ded552c2, 0x5a92f1dba88ad318, 0x239900d4ed8623b9
  ]

-- Deterministic SplitMix64 expansion varies all 26 input words.
sampleWords :: Word64 -> [Word64]
sampleWords seed = map scramble (iterate advance (advance seed))
 where
  advance x = x + 0x9e3779b97f4a7c15
  scramble x =
    let a = (x `xor` (x `shiftR` 30)) * 0xbf58476d1ce4e5b9
        b = (a `xor` (a `shiftR` 27)) * 0x94d049bb133111eb
    in b `xor` (b `shiftR` 31)

cases :: [Case]
cases =
  [ Case "RFC7693 Appendix A abc" abcState abcBlock (3,0)
  , Case "zero raw state and block" (replicate 8 0) (replicate 16 0) (0,0)
  , Case "maximum state block and counter words" (replicate 8 maxBound) (replicate 16 maxBound) (maxBound,maxBound)
  , Case "last offset before high counter carry" iv [0..15] (maxBound,0)
  , Case "first offset after high counter carry" iv [0..15] (0,1)
  , Case "swapped counter words" iv [0..15] (1,0)
  , Case "top bit of high counter word" iv [0..15] (0,2^63)
  , Case "asymmetric high and low counters" (reverse iv) [16..31] (0xfedcba9876543210,0x8123456789abcdef)
  ] ++ map generated [1..32]
 where
  generated i = case splitAt 8 (take 26 (sampleWords i)) of
    (h, rest) -> case splitAt 16 rest of
      (m, [lo,hi]) -> Case ("deterministic full-width sample " ++ show i) h m (lo,hi)
      _ -> error "expected generated counter words"

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  env <- case mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0]
                           [mkOutput 900 mempty] 0) 0 defaultTap hash0 of
    Just e -> pure e
    Nothing -> fail "could not build the evaluation environment"
  let run candidate h m counter = fmap unpack (J.fastEval candidate env (pack h m counter))
      reference counter = compressReference iv [0..15] counter True
      abcPublished = compressReference abcState abcBlock (3,0) True == abcAnswer
      finalControl = compressReference abcState abcBlock (3,0) False /= abcAnswer
      counterControl = reference (0,1) /= reference (1,0)
                    && reference (0,1) /= reference (0,0)
  putStrLn ("Independent F matches RFC Appendix A state: " ++ show abcPublished)
  putStrLn ("Final flag control distinguishes Appendix A: " ++ show finalControl)
  putStrLn ("Counter controls distinguish high, low and zero words: " ++ show counterControl)
  passed <- forM cases $ \(Case label h m counter@(lo,hi)) -> do
    let expected = Just (compressReference h m counter True)
        raw = run rawCandidate h m counter == expected
        jetted = run jettedCandidate h m counter == expected
    printf "%s\tt0=%016x\tt1=%016x\traw=%s\tjetted=%s\n"
      label lo hi (show raw) (show jetted)
    pure (raw && jetted)
  let successes = length (filter id passed)
  printf "TOTAL %d/%d inputs agree in both Simplicity paths\n" successes (length cases)
  unless (abcPublished && finalControl && counterControl && and passed) exitFailure
