-- Check one-block compression against independent whole-hash Haskell references.
module Main where

import Control.Monad (forM, unless)
import Data.Bits (shiftR)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering), hSetBuffering, stdout)
import qualified JetDiscovery.Corpus.Ed25519 as Ed
import qualified JetDiscovery.Corpus.Ripemd as Ripemd
import qualified JetDiscovery.Lib.Ripemd160 as Rmd
import qualified JetDiscovery.Ref.HmacSha512 as Sha
import JetDiscovery.Tx (defaultTap, dummyOutpoint, hex, mkEnv, mkInput, mkOutput, mkTx)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Digest (hash0)
import qualified Simplicity.Ty.Word as W

sha512IV :: [Integer]
sha512IV =
  [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
  , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
  ]

pack8 :: [a] -> W.Vector8 a
pack8 [a,b,c,d,e,f,g,h] = (((a,b),(c,d)),((e,f),(g,h)))
pack8 _ = error "expected eight words"

pack16 :: [a] -> W.Vector16 a
pack16 values = (pack8 (take 8 values),pack8 (drop 8 values))

unpack8 :: W.Vector8 a -> [a]
unpack8 (((a,b),(c,d)),((e,f),(g,h))) = [a,b,c,d,e,f,g,h]

bigEndian :: BS.ByteString -> Integer
bigEndian = BS.foldl' (\a b -> 256 * a + toInteger b) 0

littleBytes :: Int -> Integer -> BS.ByteString
littleBytes bytes value =
  BS.pack [fromInteger (value `shiftR` (8 * index)) | index <- [0..bytes-1]]

bigBytes :: Int -> Integer -> BS.ByteString
bigBytes bytes = BS.reverse . littleBytes bytes

splitWords :: Int -> (BS.ByteString -> Integer) -> BS.ByteString -> [Integer]
splitWords width readWord block
  | BS.null block = []
  | otherwise = readWord (BS.take width block) : splitWords width readWord (BS.drop width block)

padOneBlock :: Int -> BS.ByteString -> BS.ByteString -> BS.ByteString
padOneBlock blockSize encodedLength msg
  | padding < 0 = error "message exceeds one padded block"
  | otherwise = BS.snoc msg 0x80 <> BS.replicate padding 0 <> encodedLength
 where
  padding = blockSize - BS.length msg - 1 - BS.length encodedLength

shaEval :: J.FastEval J.JetType
  (W.Vector8 W.Word64,W.Vector16 W.Word64) (W.Vector8 W.Word64)
shaEval = J.unwrap (J.jetSubst Ed.sha512Compress)
{-# NOINLINE shaEval #-}

rmdEval :: J.FastEval J.JetType (Rmd.W5,W.Vector16 W.Word32) Rmd.W5
rmdEval = J.unwrap (J.jetSubst Rmd.ripemd160Compress)
{-# NOINLINE rmdEval #-}

runSha :: PrimEnv -> BS.ByteString -> Maybe BS.ByteString
runSha env msg = fmap output (J.fastEval shaEval env input)
 where
  padded = padOneBlock 128 (bigBytes 16 (8 * toInteger (BS.length msg))) msg
  input = (pack8 (map W.toWord64 sha512IV), pack16 (map W.toWord64 (splitWords 8 bigEndian padded)))
  output = BS.concat . map (bigBytes 8 . W.fromWord64) . unpack8

runRmd :: PrimEnv -> BS.ByteString -> Maybe BS.ByteString
runRmd env msg = fmap output (J.fastEval rmdEval env input)
 where
  padded = padOneBlock 64 (littleBytes 8 (8 * toInteger (BS.length msg))) msg
  littleEndian = bigEndian . BS.reverse
  input = (Rmd.toW5 Rmd.ripemdIV,pack16 (map W.toWord32 (splitWords 4 littleEndian padded)))
  output (a,(b,(c,(d,e)))) = BS.concat (map (littleBytes 4 . W.fromWord32) [a,b,c,d,e])

sample :: Int -> BS.ByteString
sample 3 = BC.pack "abc"
sample size = BS.pack (take size (iterate (+73) 0xa7))

check :: String
      -> (BS.ByteString -> Maybe BS.ByteString)
      -> (BS.ByteString -> BS.ByteString)
      -> [Int] -> IO [Bool]
check name actual reference lengths = forM lengths $ \size -> do
  let msg = sample size
      expected = reference msg
      observed = actual msg
      passed = observed == Just expected
  putStrLn (name ++ "\tmessageBytes=" ++ show size
            ++ "\treference=" ++ hex expected
            ++ "\tcompressor=" ++ maybe "failed" hex observed
            ++ "\tpass=" ++ show passed)
  pure passed

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  env <- case mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0]
                           [mkOutput 900 mempty] 0) 0 defaultTap hash0 of
    Just e -> pure e
    Nothing -> fail "could not build the evaluation environment"
  sha <- check "SHA512" (runSha env) Sha.sha512 [0,1,3,7,8,63,64,110,111]
  rmd <- check "RIPEMD160" (runRmd env) Ripemd.ripemd160Ref [0,1,3,4,7,8,31,32,54,55]
  let summary name results = putStrLn
        (name ++ " " ++ show (length (filter id results)) ++ "/" ++ show (length results) ++ " agree")
  summary "SHA512" sha
  summary "RIPEMD160" rmd
  unless (and sha && and rmd) exitFailure
