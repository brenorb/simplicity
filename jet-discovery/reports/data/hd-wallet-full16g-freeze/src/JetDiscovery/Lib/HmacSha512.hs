{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | RFC2104 HMAC-SHA512 for the exact BIP32 CKDpub input format.
-- A32-byte key and37-byte data enter once; no witnessed midstates/digests.
module JetDiscovery.Lib.HmacSha512 (hmac37,HmacInput) where

import Prelude hiding (drop,take)
import qualified Prelude as P
import Data.Bits (testBit)
import Simplicity.Term.Core
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Programs.Word as W
import Simplicity.Ty.Word hiding (Vector)
import qualified Simplicity.Ty.Word as T
import JetDiscovery.Corpus.Ed25519 (sha512Compress)
import JetDiscovery.Lib.Bytes

-- | (chainCode,(compressedKeyPrefix,(publicKeyX,BEchildIndex))).
-- This hash helper deliberately leaves prefix/index/key policy to its caller.
type HmacInput=(Word256,(Word8,(Word256,Word32)))

pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t(a,a)b
pick True=drop
pick False=take
byte256 :: Core t => Int -> t Word256 Word8
byte256 i=pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))))
byte32 :: Core t => Int -> t Word32 Word8
byte32 i=pick(testBit i 1)(pick(testBit i 0)iden)
pack :: (Core t,TyC a) => T.Vector Word8 v -> [t a Word8] -> t a v
pack SingleV [x]=x
pack (DoubleV v) xs=pack v(P.take n xs)&&&pack v(P.drop n xs)
 where n=vectorSize v
pack _ _=error "HMAC fixed byte packing"

iv :: (Core t,TyC a) => t a Word512
iv=konst(toWord word512 0x6a09e667f3bcc908bb67ae8584caa73b3c6ef372fe94f82ba54ff53a5f1d36f1510e527fade682d19b05688c2b3e6c1f1f83d9abfb41bd6b5be0cd19137e2179)

-- Cache a single compression frontend, never a whole HMAC/application DAG.
{-# NOINLINE compressionWrapped #-}
compressionWrapped :: J.WrappedSimplicity (Word512,Word1024) Word512
compressionWrapped=J.jetSubst sha512Compress
compression :: Simplicity t => t(Word512,Word1024)Word512
compression=J.unwrap compressionWrapped

keyState :: Simplicity t => Integer -> t Word256 Word512
keyState padByte=(iv&&&(paddedKey>>>xorPad))>>>compression
 where
  z=konst(w256 0)
  paddedKey=(iden&&&z)&&&(z&&&z)
  mask=padByte*P.sum[256^i|i<-[0..127::Int]]
  xorPad=(iden&&&konst(toWord word1024 mask))>>>W.bitwise_xor word1024

messageBlock :: Core t => t(Word8,(Word256,Word32))Word1024
messageBlock=pack vector128[at i|i<-[0..127]]
 where
  at 0=oh
  at i | i<=32=drop(take(byte256(i-1)))
       | i<=36=drop(drop(byte32(i-33)))
       | i==37=konst(w8 0x80)
       -- SHA512 length counts the preceding128-byte ipad block too.
       | i==126=konst(w8 5)
       | i==127=konst(w8 0x28)
       | otherwise=konst(w8 0)

hmac37 :: Simplicity t => t HmacInput Word512
hmac37=(iden&&&take(keyState 0x36))>>>
 ((oh>>>oh)&&&((ih&&&(oh>>>drop messageBlock))>>>compression))>>>
 ((take(keyState 0x5c))&&&(ih&&&konst(toWord word512(2^(511::Int)+1536))))>>>
 compression
