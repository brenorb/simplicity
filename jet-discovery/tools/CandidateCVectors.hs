{-# LANGUAGE GADTs, RankNTypes #-}
-- | Bit-exact frame vectors for the standalone C candidate sketches in bench/.
--
-- For every candidate in "JetDiscovery.Candidates.Registry" this evaluates the
-- unjetted Simplicity reference expression on generated inputs and prints one
-- line per vector:
--
-- > name <TAB> input-hex <TAB> OK|FAIL <TAB> output-hex <TAB> output-mask-hex
--
-- Hex strings hold Bit Machine cells MSB-first, zero-padded to whole bytes.
-- Sum-type padding cells are written as 0 in the input and are masked out (0)
-- in the output mask, so the C sketch must agree on every defined cell.
--
-- Usage: candidate-c-vectors [COUNT] [NAME...]   (default COUNT 400, all names)
module Main where

import Control.Monad (forM_, replicateM)
import Data.Bits (shiftL, shiftR, testBit, xor, (.&.), (.|.))
import Data.Char (intToDigit)
import Data.List (unfoldr)
import qualified Data.ByteString as BS
import System.Environment (getArgs)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

import Simplicity.Ty
import Simplicity.BitMachine (Cell, encode)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Primitive (PrimEnv)

import JetDiscovery.JetSets (Candidate(..), SomeCandidate(..))
import JetDiscovery.Candidates.Registry (candidates)
import JetDiscovery.Tx

-- A small deterministic generator (SplitMix64), so vectors are reproducible
-- without extra package dependencies.
newtype Gen a = Gen { runGen :: Integer -> (a, Integer) }
instance Functor Gen where fmap f (Gen g) = Gen (\s -> let (a, s') = g s in (f a, s'))
instance Applicative Gen where
  pure a = Gen (\s -> (a, s))
  Gen f <*> Gen g = Gen (\s -> let (h, s1) = f s; (a, s2) = g s1 in (h a, s2))
instance Monad Gen where
  Gen g >>= k = Gen (\s -> let (a, s1) = g s in runGen (k a) s1)

mask64 :: Integer
mask64 = 2^(64::Int) - 1

next64 :: Gen Integer
next64 = Gen step
 where
  step s = let s' = (s + 0x9e3779b97f4a7c15) `mod` 2^(64::Int)
               z1 = ((s' `xorI` (s' `shiftR` 30)) * 0xbf58476d1ce4e5b9) `mod` 2^(64::Int)
               z2 = ((z1 `xorI` (z1 `shiftR` 27)) * 0x94d049bb133111eb) `mod` 2^(64::Int)
           in (z2 `xorI` (z2 `shiftR` 31), s')
  xorI = xor

bitsN :: Int -> Gen Integer
bitsN n = do
  ws <- replicateM ((n + 63) `div` 64) next64
  let v = foldl (\acc w -> acc `shiftL` 64 .|. (w .&. mask64)) 0 ws
  return (v `mod` 2^n)

below :: Integer -> Gen Integer
below k = (`mod` k) <$> bitsN 64

-- Moduli that appear in candidate specifications; values near them exercise
-- the canonical/non-canonical boundary.
interesting :: [Integer]
interesting =
  [ 2^(31::Int) - 1                                                     -- M31
  , 2130706433                                                          -- KoalaBear
  , 2^(255::Int) - 19                                                   -- ed25519
  , 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff  -- P-256 p
  , 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551  -- P-256 n
  , 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47  -- BN254 p
  , 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f  -- secp256k1 p
  , 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141  -- secp256k1 n
  ]

-- | A value for an n-bit word, drawn from one of several families.
wordValue :: Int -> Gen Integer
wordValue n = do
  family <- below 8
  let top = 2^n
  case family of
    0 -> return 0
    1 -> return (top - 1)
    2 -> below 256
    3 -> do k <- below (toInteger n); d <- below 5; return ((2^k + d - 2) `mod` top)
    4 -> do let cands = [ m | m <- interesting, m < top, m * 2 >= 2^(min n 32) ]
            if null cands then bitsN n else do
              i <- below (toInteger (length cands)); d <- below 5
              return ((cands !! fromInteger i + d - 2) `mod` top)
    _ -> bitsN n

-- | Generate a value of any type.  Word types (at any nesting) are filled as a
-- whole by 'wordValue', so families apply to every field independently.
genValue :: TyReflect a -> Gen a
genValue r = case wordWidth r of
  Just n | n > 1 -> fromBits r <$> (toBitsBE n <$> wordValue n)
  _ -> case r of
    OneR -> return ()
    SumR a b -> do t <- below 2; if t == 0 then Left <$> genValue a else Right <$> genValue b
    ProdR a b -> (,) <$> genValue a <*> genValue b

wordWidth :: TyReflect a -> Maybe Int
wordWidth (SumR OneR OneR) = Just 1
wordWidth (ProdR a b) = do { n <- wordWidth a; m <- wordWidth b; if n == m then Just (n + m) else Nothing }
wordWidth _ = Nothing

toBitsBE :: Int -> Integer -> [Bool]
toBitsBE n v = [ testBit v i | i <- [n-1, n-2 .. 0] ]

-- Build a word-shaped value from big-endian bits.
fromBits :: TyReflect a -> [Bool] -> a
fromBits r bs = case go r bs of (v, []) -> v; _ -> error "fromBits: length"
 where
  go :: TyReflect a -> [Bool] -> (a, [Bool])
  go OneR l = ((), l)
  go (SumR OneR OneR) (b:l) = (if b then Right () else Left (), l)
  go (ProdR a b) l = let (x, l1) = go a l; (y, l2) = go b l1 in ((x, y), l2)
  go _ _ = error "fromBits: not a word"

allSame :: Bool -> TyReflect a -> a
allSame b r = case r of
  OneR -> ()
  SumR a c -> if b then Right (allSame b c) else Left (allSame b a)
  ProdR a c -> (allSame b a, allSame b c)

hexCells :: [Cell] -> (String, String)
hexCells cells = (hex (map (maybe False id) cells), hex (map (maybe False (const True)) cells))
 where
  hex bs = concatMap byte (chunk (bs ++ replicate ((8 - length bs `mod` 8) `mod` 8) False))
  chunk = unfoldr (\l -> if null l then Nothing else Just (splitAt 8 l))
  byte b8 = let v = foldl (\acc x -> 2*acc + fromEnum x) 0 b8 in [intToDigit (v `div` 16), intToDigit (v `mod` 16)]

env :: PrimEnv
env = case mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap (hashFromInteger 0) of
  Just e -> e
  Nothing -> error "environment"

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  let (count, names) = case args of
        (a:rest) | all (`elem` "0123456789") a -> (read a, rest)
        rest -> (400, rest)
  forM_ candidates $ \(SomeCandidate c) -> emit count names c

emit :: (TyC a, TyC b) => Int -> [String] -> Candidate a b -> IO ()
emit count names c@(Candidate name _ spec)
  | not (null names) && name `notElem` names = return ()
  | otherwise = forM_ inputs $ \x -> do
      let (ih, _) = hexCells (encode x)
      case J.fastEval (J.unwrap (J.jetSubst spec)) env x of
        Nothing -> putStrLn (name ++ "\t" ++ ih ++ "\tFAIL\t-\t-")
        Just y -> let (oh, om) = hexCells (encode y) in putStrLn (name ++ "\t" ++ ih ++ "\tOK\t" ++ oh ++ "\t" ++ om)
 where
  ra = inputRefl c
  seed = toInteger (BS.foldl' (\h w -> (h * 31 + fromIntegral w) `mod` 2^(61::Int)) 7 (BS.pack (map (toEnum . fromEnum) name)))
  inputs = allSame False ra : allSame True ra : fst (runGen (replicateM count (genValue ra)) seed)
  inputRefl :: (TyC a, TyC b) => Candidate a b -> TyReflect a
  inputRefl _ = reify
