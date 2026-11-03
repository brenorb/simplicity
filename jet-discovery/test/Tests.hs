-- | Checks that each candidate jet's Simplicity specification (a corpus
-- kernel) agrees with an independent Haskell reference, and that the
-- BIP 340 reference signer reproduces the official test vectors.
module Main (main) where


import Data.Bits (xor, (.&.), complement, rotateL, rotateR, shiftL, shiftR)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Word (Word32, Word64)
import qualified Data.List as L
import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)

import Simplicity.Term.Core ((>>>), (&&&), iden)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Primitive (PrimEnv)
import Simplicity.Digest (hash0)
import qualified Simplicity.Ty.Word as W

import JetDiscovery.Lib.Bytes (konst, w8, w32, w64, w256FromBytes, w256ToBytes)
import JetDiscovery.Lib.Kernels (sha256Pair, wotsChain)
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark
import qualified JetDiscovery.Ref.Bip340 as Bip340
import qualified JetDiscovery.Ref.Shrincs as Shrincs
import qualified JetDiscovery.Corpus.P256 as P256
import qualified JetDiscovery.Corpus.Ripemd as Ripemd
import qualified JetDiscovery.Lib.Ripemd160 as Rmd
import qualified JetDiscovery.Corpus.Ed25519 as Ed
import qualified Data.ByteString.Char8 as BSC8
import JetDiscovery.Tx

env :: PrimEnv
env = maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)

run :: Jets.FastEval Jets.JetType a b -> a -> Maybe b
run t = Jets.fastEval t env

-- deterministic pseudo-random integers (64-bit LCG)
rands :: Integer -> [Integer]
rands seed = tail (iterate (\x -> (x * 6364136223846793005 + 1442695040888963407) `mod` 2 ^ (64 :: Int)) seed)

main :: IO ()
main = defaultMain $ testGroup "jet-discovery"
  [ bip340Tests
  , p256Tests
  , testCase "RIPEMD-160 reference reproduces the published digests" $ do
      Ripemd.ripemd160Ref BS.empty @?= unhex "9c1185a5c5e9fc54612808977ee8f548b2258d31"
      Ripemd.ripemd160Ref (BSC8.pack "abc") @?= unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
      Ripemd.ripemd160Ref (BSC8.pack "message digest") @?= unhex "5d0689ef49d2fae572b881b123a85ffa21595f36"
  , testGroup "candidate specifications agree with Haskell references"
    [ testCase "m31_mul" $ do
        let xs = take 40 [ (a `mod` Stark.p31, b `mod` Stark.p31) | (a, b) <- pairs (rands 1) ]
        mapM_ (\(a, b) -> fmap W.fromWord32 (run Stark.m31Mul (W.toWord32 a, W.toWord32 b)) @?= Just (Stark.hMul a b)) xs
    , testCase "qm31_mul" $ do
        let qs = take 10 [ ((a, b), (c, d)) | [a, b, c, d] <- chunks 4 (map (`mod` Stark.p31) (rands 2)) ]
        mapM_ (\(x, y) -> run Stark.qm31Mul (Stark.toQ x, Stark.toQ y) @?= Just (Stark.toQ (Stark.hQMul x y))) (zip qs (reverse qs))
    , testCase "sha256_pair" $ do
        let bs = BS.pack (map fromIntegral (take 64 (rands 3)))
        fmap w256ToBytes (run sha256Pair (W.toWord512 (Bip340.intFromBytes bs))) @?= Just (hashToBytes (sha256 bs))
    , testCase "sha256_wots_chain_16" $ do
        let pkSeed = BS.replicate 16 0x5e
            (h, idx, chain) = (251, 5, 7)
            prefix = ctx8Init &&& konst (W.toWord512 (Bip340.intFromBytes (pkSeed <> BS.replicate 48 0))) >>> ctx8Add64
                 >>> (iden &&& konst (w8 h) >>> ctx8Add1) >>> (iden &&& konst (w64 idx) >>> ctx8Add8)
                 >>> (iden &&& konst (w8 16) >>> ctx8Add1) >>> (iden &&& konst (w32 0) >>> ctx8Add4)
                 >>> (iden &&& konst (w32 chain) >>> ctx8Add4)
            Just ctx = run prefix ()
            node = BS.pack [1 .. 16]
        mapM_ (\start -> fmap (\w -> BS.drop 16 (Bip340.bytesFromInt (W.fromWord128 w)))
                              (run wotsChain (ctx, (W.toWord4 (toInteger start), W.toWord128 (Bip340.intFromBytes node))))
                         @?= Just (Shrincs.wotsChainIter node start 15 pkSeed (fromInteger h) idx chain)) [0, 1, 7, 15]
    , testCase "keccak_f1600" $ do
        let st = take 25 (map fromInteger (rands 4)) :: [Word64]
            toV ls = vec32 (map (W.toWord64 . toInteger) (ls ++ replicate 7 0))
        fmap (map (fromInteger . W.fromWord64) . take 25 . unvec32) (run Hashes.keccakF (toV st)) @?= Just (keccakRef st)
    , testCase "blake2s_compress" $ do
        let hs = map fromInteger (take 8 (rands 5)) :: [Word32]
            ms = map fromInteger (take 16 (rands 6)) :: [Word32]
            v8 = vec8 . map (W.toWord32 . toInteger)
        fmap (map (fromInteger . W.fromWord32) . unvec8) (run (Hashes.blake2F Hashes.blake2s) ((v8 hs, (v8 (take 8 ms), v8 (drop 8 ms))), (W.toWord32 64, W.toWord32 0)))
          @?= Just (blake2sRef hs ms 64)
    , testCase "div_mod_256 and multiply_128" $ do
        let xs = take 20 (pairs (map (\x -> x * x * x * x) (rands 7)))
        mapM_ (\(a, b) -> do
                 let a' = a `mod` 2 ^ (256 :: Int); b' = 1 + b `mod` 2 ^ (200 :: Int)
                 fmap (\(q, r) -> (W.fromWord256 q, W.fromWord256 r)) (run (Arith.div_mod W.word256) (W.toWord256 a', W.toWord256 b')) @?= Just (a' `divMod` b')
                 let c = a `mod` 2 ^ (128 :: Int); d = b `mod` 2 ^ (128 :: Int)
                 fmap W.fromWord256 (run (Arith.multiply W.word128) (W.toWord128 c, W.toWord128 d)) @?= Just (c * d)) xs
    , testCase "multiply_256 and div_mod_512" $ do
        let xs = take 12 (pairs (map (\x -> x ^ (8 :: Int) + x) (rands 11)))
        mapM_ (\(a, b) -> do
                 let a' = a `mod` 2 ^ (256 :: Int); b' = b `mod` 2 ^ (256 :: Int)
                 fmap W.fromWord512 (run (Arith.multiply W.word256) (W.toWord256 a', W.toWord256 b')) @?= Just (a' * b')
                 let n = a' * b' + b'; d = 1 + b' `mod` 2 ^ (190 :: Int)
                 fmap (\(q, r) -> (W.fromWord512 q, W.fromWord512 r)) (run (Arith.div_mod W.word512) (W.toWord512 n, W.toWord512 d)) @?= Just (n `divMod` d)) xs
    , testCase "ripemd160_compress (one padded block of \"abc\")" $ do
        let le bs = sum [ toInteger b * 256 ^ i | (i, b) <- zip [0 :: Int ..] (BS.unpack bs) ]
            wordsLE bs = [ le (BS.take 4 (BS.drop (4 * i) bs)) | i <- [0 .. BS.length bs `div` 4 - 1] ]
            blk = wordsLE (BSC8.pack "abc\x80" <> BS.replicate 52 0) ++ [24, 0]
            v16 ws = (vec8 (map W.toWord32 (take 8 ws)), vec8 (map W.toWord32 (drop 8 ws)))
            out = run Rmd.ripemd160Compress (Rmd.toW5 Rmd.ripemdIV, v16 blk)
            flat (a, (b, (c, (d, e)))) = map W.fromWord32 [a, b, c, d, e]
        fmap flat out @?= Just (wordsLE (unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"))
    , testCase "sha512_compress (one padded block of \"abc\", FIPS 180-4)" $ do
        let be bs = foldl (\acc b -> acc * 256 + toInteger b) 0 (BS.unpack bs)
            words64 bs = [ be (BS.take 8 (BS.drop (8 * i) bs)) | i <- [0 .. BS.length bs `div` 8 - 1] ]
            iv = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]
            blk = words64 (BSC8.pack "abc\x80" <> BS.replicate 116 0) ++ [24]
            v8' = vec8 . map W.toWord64
        fmap (map W.fromWord64 . unvec8) (run Ed.sha512Compress (v8' iv, (v8' (take 8 blk), v8' (drop 8 blk))))
          @?= Just (words64 (unhex "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"))
    , testCase "ed25519_fe_multiply" $ do
        let p = 2 ^ (255 :: Int) - 19
            xs = take 30 [ (a `mod` p, b `mod` p) | (a, b) <- pairs (map (\x -> x ^ (5 :: Int) + x) (rands 13)) ] ++ [(p - 1, p - 1), (0, p - 1), (1, 1)]
        mapM_ (\(a, b) -> fmap W.fromWord256 (run Ed.mulmod (W.toWord256 a, W.toWord256 b)) @?= Just (a * b `mod` p)) xs
    ]
  ]
 where
  pairs (a:b:r) = (a, b) : pairs r
  pairs _ = []
  chunks n xs = let (a, b) = splitAt n xs in a : chunks n b

-- BIP 340 vectors ----------------------------------------------------------------

bip340Tests :: TestTree
bip340Tests = testCase "Ref.Bip340 reproduces bip-0340_test-vectors.csv" $ do
  rows <- map (splitOn ',') . drop 1 . lines <$> readFile "vendor-specs/bips/bip-0340_test-vectors.csv"
  mapM_ check rows
 where
  check (i:sk:pk:aux:msg:sig:res:_) = do
    let ok = Bip340.verify (unhex pk) (unhex msg) (unhex sig)
    assertBool ("verify row " ++ i) (ok == (res == "TRUE"))
    if null sk then return () else do
      let s = Bip340.sign (Bip340.intFromBytes (unhex sk)) (unhex msg) (unhex aux)
      assertBool ("sign row " ++ i) (s == unhex sig)
  check r = assertBool ("bad row " ++ show r) False
  splitOn c s = case break (== c) s of
    (a, []) -> [a]
    (a, _:r) -> a : splitOn c r

-- Haskell references ---------------------------------------------------------------

keccakRef :: [Word64] -> [Word64]
keccakRef st0 = foldl roundF st0 [0 .. 23]
 where
  rc = [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
       , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
       , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
       , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]
  rot x y = [[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]] !! x !! y
  at a x y = a !! (x + 5 * y)
  roundF a r = iota
   where
    c x = foldr1 xor [ at a x y | y <- [0 .. 4] ]
    d x = c ((x + 4) `mod` 5) `xor` (c ((x + 1) `mod` 5) `rotateL` 1)
    th = [ at a x y `xor` d x | y <- [0 .. 4], x <- [0 .. 4] ]
    b = [ head [ (at th x y) `rotateL` rot x y | x <- [0 .. 4], y <- [0 .. 4], y' == y && x' == (2 * x + 3 * y) `mod` 5 ]
        | y' <- [0 .. 4], x' <- [0 .. 4] ]
    -- b is indexed [x' + 5 y'] with B[y, 2x+3y] = rot(A[x,y]): position (x'=y? ) handled below
    bArr = [ head [ (at th x y) `rotateL` rot x y | x <- [0 .. 4], y <- [0 .. 4], y + 5 * ((2 * x + 3 * y) `mod` 5) == j ] | j <- [0 .. 24] ]
    chi = [ (bArr !! (x + 5 * y)) `xor` (complement (bArr !! (((x + 1) `mod` 5) + 5 * y)) .&. (bArr !! (((x + 2) `mod` 5) + 5 * y))) | y <- [0 .. 4], x <- [0 .. 4] ]
    iota = (head chi `xor` (rc !! r)) : tail chi

blake2sRef :: [Word32] -> [Word32] -> Word32 -> [Word32]
blake2sRef h m t = [ (h !! i) `xor` (v !! i) `xor` (v !! (i + 8)) | i <- [0 .. 7] ]
 where
  iv = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
  sigma = [ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15], [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3]
          , [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4], [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8]
          , [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13], [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9]
          , [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11], [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10]
          , [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5], [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0] ]
  v0 = h ++ take 4 iv ++ [iv !! 4 `xor` t, iv !! 5, complement (iv !! 6), iv !! 7]
  v = foldl rnd v0 [0 .. 9]
  set vs i x = take i vs ++ [x] ++ drop (i + 1) vs
  g vs (a, b, c, d) x y =
    let va1 = vs !! a + vs !! b + x; vd1 = (vs !! d `xor` va1) `rotateR` 16; vc1 = vs !! c + vd1; vb1 = (vs !! b `xor` vc1) `rotateR` 12
        va2 = va1 + vb1 + y; vd2 = (vd1 `xor` va2) `rotateR` 8; vc2 = vc1 + vd2; vb2 = (vb1 `xor` vc2) `rotateR` 7
    in set (set (set (set vs a va2) b vb2) c vc2) d vd2
  rnd vs r = let s = sigma !! r
                 ls = [(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]
             in foldl (\acc (i, l) -> g acc l (m !! (s !! (2 * i))) (m !! (s !! (2 * i + 1)))) vs (zip [0 ..] ls)

-- nested-pair vectors
vec8 :: [a] -> ((((a, a), (a, a)), ((a, a), (a, a))))
vec8 [a, b, c, d, e, f, g, h] = (((a, b), (c, d)), ((e, f), (g, h)))
vec8 _ = error "vec8"
unvec8 :: ((((a, a), (a, a)), ((a, a), (a, a)))) -> [a]
unvec8 (((a, b), (c, d)), ((e, f), (g, h))) = [a, b, c, d, e, f, g, h]
vec32 :: [a] -> (((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))), ((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))))
vec32 xs = ((vec8 (s 0), vec8 (s 1)), (vec8 (s 2), vec8 (s 3))) where s i = take 8 (drop (8 * i) xs)
unvec32 :: (((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))), ((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a))))) -> [a]
unvec32 ((a, b), (c, d)) = concatMap unvec8 [a, b, c, d]

-- P-256 field and group operations ------------------------------------------------------------

p256Tests :: TestTree
p256Tests = testGroup "P-256 Simplicity arithmetic agrees with Integer arithmetic"
  [ testCase "mulmod" $ mapM_ (\(a, b) -> fmap W.fromWord256 (run P256.mulmod (W.toWord256 a, W.toWord256 b)) @?= Just (a * b `mod` p)) xs
  , testCase "addmod and submod" $ mapM_ (\(a, b) -> do
        fmap W.fromWord256 (run P256.addmod (W.toWord256 a, W.toWord256 b)) @?= Just ((a + b) `mod` p)
        fmap W.fromWord256 (run P256.submod (W.toWord256 a, W.toWord256 b)) @?= Just ((a - b) `mod` p)) xs
  , testCase "dblJ and maddJ" $ do
        let j = ((gx, gy), 1)
            Just d = run P256.dblJ (toJ j)
            Just a = run P256.maddJ (d, (W.toWord256 gx, W.toWord256 gy))
        affine (fromJ d) @?= affine (dblRef (gx, gy))
        affine (fromJ a) @?= affine (addRef (dblRef (gx, gy)) (gx, gy))
  ]
 where
  p = P256.pP256
  gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  xs = take 30 [ (a `mod` p, b `mod` p) | (a, b) <- pairs (map (\x -> x * x * x * x + x) (rands 9)) ] ++ [(p - 1, p - 1), (0, p - 1), (1, 1)]
  pairs (a:b:r) = (a, b) : pairs r
  pairs _ = []
  inv x = powM x (p - 2)
  powM _ 0 = 1
  powM b e | even e = let h = powM b (e `div` 2) in h * h `mod` p
           | otherwise = b * powM b (e - 1) `mod` p
  toJ ((x, y), z) = ((W.toWord256 x, W.toWord256 y), W.toWord256 z)
  fromJ ((x, y), z) = ((W.fromWord256 x, W.fromWord256 y), W.fromWord256 z)
  affine ((x, y), z) = (x * inv (z * z) `mod` p, y * inv (z * z * z) `mod` p)
  dblRef (x, y) = let l = (3 * x * x - 3) * inv (2 * y) `mod` p; x3 = (l * l - 2 * x) `mod` p in ((x3, (l * (x - x3) - y) `mod` p), 1)
  addRef ((x1, y1), _) (x2, y2) = let l = (y2 - y1) * inv (x2 - x1) `mod` p; x3 = (l * l - x1 - x2) `mod` p in ((x3, (l * (x1 - x3) - y1) `mod` p), 1)
