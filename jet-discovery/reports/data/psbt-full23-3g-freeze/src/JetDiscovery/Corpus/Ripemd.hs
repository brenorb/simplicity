{-# LANGUAGE ScopedTypeVariables #-}
-- | RIPEMD-160 and HASH160 (RIPEMD160(SHA256(x))), which Bitcoin Script uses
-- for P2PKH/P2WPKH key hashes and BOLT 3 HTLC payment hashes.  Bitcoin
-- Simplicity has no RIPEMD-160 jet.
module JetDiscovery.Corpus.Ripemd
  ( entries
  , ripemd160Compress
  , ripemd160Ref
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Bits as B
import qualified Data.List as L
import qualified Data.Word as DW

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.Bitcoin.Term (Simplicity, Primitive)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.Ripemd160
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref


-- | HASH160 of a 32-byte value: RIPEMD160 of the single padded block holding SHA256(x).
hash160Of32 :: Assert term => term Word256 W5
hash160Of32 = sha >>> (ivT &&& block) >>> ripemd160Compress
 where
  sha = (unit >>> ctx8Init) &&& iden >>> ctx8Add32 >>> ctx8Finalize
  -- the 8 big-endian words of the hash, byte-swapped to little endian, then padding and the bit length (256)
  word i = pick (i >= 4) (pick (odd (i `div` 2)) (pick (odd i) iden)) >>> bswap32
  block = mk16 ([ word i | i <- [0 .. 7] ] ++ [konst (w32 0x80)] ++ replicate 5 (konst (w32 0)) ++ [konst (w32 256), konst (w32 0)])

-- Haskell reference ------------------------------------------------------------------

ripemd160Ref :: BS.ByteString -> BS.ByteString
ripemd160Ref msg = BS.concat (map le32 (L.foldl' compress (map fromInteger ripemdIV) blocks))
 where
  ml = BS.length msg
  padded = msg <> BS.pack [0x80] <> BS.replicate ((55 - ml) `mod` 64) 0 <> BS.pack [ fromIntegral ((8 * ml) `B.shiftR` (8 * i)) | i <- [0 .. 7] ]
  blocks = [ [ le (BS.take 4 (BS.drop (4 * w) (BS.take 64 (BS.drop (64 * b) padded)))) | w <- [0 .. 15] ] | b <- [0 .. BS.length padded `div` 64 - 1] ]
  le = BS.foldr (\x a -> a * 256 + fromIntegral x) 0 :: BS.ByteString -> DW.Word32
  le32 w = BS.pack [ fromIntegral (w `B.shiftR` (8 * i)) | i <- [0 .. 3] ]
  fn :: Int -> DW.Word32 -> DW.Word32 -> DW.Word32 -> DW.Word32
  fn 0 x y z = x `B.xor` y `B.xor` z
  fn 1 x y z = (x B..&. y) B..|. (B.complement x B..&. z)
  fn 2 x y z = (x B..|. B.complement y) `B.xor` z
  fn 3 x y z = (x B..&. z) B..|. (y B..&. B.complement z)
  fn _ x y z = x `B.xor` (y B..|. B.complement z)
  runLine xs rs ss ks g0 st = L.foldl' (\[a, b, c, d, e] j ->
      let g = g0 (j `div` 16)
          t = B.rotateL (a + fn g b c d + xs !! (rs !! j) + fromInteger (ks !! (j `div` 16))) (ss !! j) + e
      in [e, t, b, B.rotateL c 10, d]) st [0 .. 79]
  compress h xs = let [aL, bL, cL, dL, eL] = runLine xs rL sL kL id h
                      [aR, bR, cR, dR, eR] = runLine xs rR sR kR (\g -> 4 - g) h
                      [h0, h1, h2, h3, h4] = h
                  in [h1 + cL + dR, h2 + dL + eR, h3 + eL + aR, h4 + aL + bR, h0 + bL + cR]

leWords5 :: BS.ByteString -> W5
leWords5 bs = toW5 [ BS.foldr (\x a -> a * 256 + toInteger x) 0 (BS.take 4 (BS.drop (4 * i) bs)) | i <- [0 .. 4] ]

-- Programs --------------------------------------------------------------------------

type SigW = (Word256, Word256)

-- | BOLT 3 offered-HTLC logic with Script's payment-hash check:
-- claim with RIPEMD160(SHA256(preimage)) == H and A's signature, or refund to B after a height.
htlc160 :: (Simplicity term, Primitive term) => W5 -> Word256 -> Word256 -> DW.Word32 -> Either (Word256, SigW) SigW -> term () ()
htlc160 h pkA pkB timeout w = witness w &&& msg >>> match claim refund
 where
  msg = unwrap (Jets.jetSubst SigHash.sigAllHash)
  chk pk s m = (konst pk &&& m) &&& s >>> Secp.bip_0340_verify
  claim = (take (take hash160Of32) &&& konst h >>> eq >>> verify) &&& chk pkA oih ih >>> unit
  refund = (konst (w32 (toInteger timeout)) >>> TL.checkLockHeight) &&& chk pkB oh ih >>> unit

entries :: [Entry]
entries =
  [ Entry
    { entryId = "xchain-ripemd160"
    , entryTitle = "RIPEMD-160 compression of a one-block message"
    , entrySpec = "RIPEMD-160 (Dobbertin, Bosselaers, Preneel 1996); Bitcoin Script's OP_RIPEMD160"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "the published RIPEMD-160 answers for \"\" and \"abc\", also reproduced by the Haskell reference in cabal test"
    , entryAssumptions = ["message of at most 55 bytes (one padded block); block and expected digest are witness operands"]
    , entryProgram = \(blk, d) -> Prog (witness (blockOf blk, leWords5 d) >>> ((ivT &&& oh) >>> ripemd160Compress) &&& ih >>> eq >>> verify)
    , entryVectors =
        [ Vector "RIPEMD-160(\"\")" anyEnv (BS.empty, unhex "9c1185a5c5e9fc54612808977ee8f548b2258d31") Accept
        , Vector "RIPEMD-160(\"abc\")" anyEnv (BSC.pack "abc", unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc") Accept
        , Vector "wrong digest" anyEnv (BSC.pack "abd", unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc") Reject ]
    }
  , Entry
    { entryId = "app-htlc-hash160"
    , entryTitle = "BOLT 3-style HTLC with HASH160 payment hash"
    , entrySpec = "BOLT 3 offered HTLC: OP_HASH160 <RIPEMD160(payment_hash)> (payment_hash = SHA256(preimage))"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "HASH160 from the Haskell RIPEMD-160 reference; signatures from JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["32-byte preimage", "absolute block-height timeout"]
    , entryProgram = progH
    , entryVectors =
        [ Vector "claim with preimage" (envH 100) (Left (w256FromBytes preimage, sigH skA 100)) Accept
        , Vector "claim with wrong preimage" (envH 100) (Left (w256 9, sigH skA 100)) Reject
        , Vector "refund after timeout" (envH 600) (Right (sigH skB 600)) Accept
        , Vector "refund before timeout" (envH 400) (Right (sigH skB 400)) Reject ]
    }
  ]
 where
  anyEnv = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  blockOf m = let ml = BS.length m
                  padded = m <> BS.pack [0x80] <> BS.replicate (55 - ml) 0 <> BS.pack [ fromIntegral ((8 * ml) `B.shiftR` (8 * i)) | i <- [0 .. 7] ]
                  ws = [ BS.foldr (\x a -> a * 256 + toInteger x) 0 (BS.take 4 (BS.drop (4 * i) padded)) | i <- [0 .. 15] ]
                  v8 [a, b, c, d, e, f, g, h] = (((w32 a, w32 b), (w32 c, w32 d)), ((w32 e, w32 f), (w32 g, w32 h)))
                  v8 _ = error "v8"
              in (v8 (L.take 8 ws), v8 (L.drop 8 ws))
  skA = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
  skB = 0xC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9
  preimage = BS.replicate 32 0x42
  h160 = leWords5 (ripemd160Ref (hashToBytes (sha256 preimage)))
  progH w = Prog (htlc160 h160 (w256 (Ref.pubkeyOf skA)) (w256 (Ref.pubkeyOf skB)) 500 w)
  cmrH = progCmr (progH (Right (w256 0, w256 0)))
  envH lock = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 (unhex "0014" <> BS.replicate 20 1)] lock) 0 defaultTap
  sigH sk lock = case envH lock cmrH >>= \e -> Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e () of
    Just m -> let Sig r s = signMsg sk (w256ToBytes m) in (toWord256 (toInteger r), toWord256 (toInteger s))
    Nothing -> error "sigH"
