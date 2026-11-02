{-# LANGUAGE ScopedTypeVariables #-}
-- | Byte-level helpers written in Simplicity: endianness swaps, buffer
-- lengths, Bitcoin CompactSize prefixes and SHA-256 over witness buffers.
--
-- Every helper is built from library expressions whose forms match existing
-- jet specifications, so 'jetSubst' finds the jets inside them.
module JetDiscovery.Lib.Bytes
  ( bswap16, bswap32, bswap64
  , isSome, failure, konst
  , buf511Len, buf63Len
  , ctxAddCompactSize511
  , ctxAddVarString511
  , ctxAddLE32, ctxAddLE64
  , sha256Buffer511
  , ctxFinalizeHash
  , buffer511FromBytes, buffer63FromBytes
  , w8, w16, w32, w64, w256
  , w256FromBytes, w256ToBytes
  ) where

import Prelude hiding (drop, take, not, and, or, subtract)
import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, (.&.))

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word

-- | Reverse the byte order of a 16 bit word.
bswap16 :: Core term => term Word16 Word16
bswap16 = ih &&& oh

bswap32 :: Core term => term Word32 Word32
bswap32 = drop bswap16 &&& take bswap16

bswap64 :: Core term => term Word64 Word64
bswap64 = drop bswap32 &&& take bswap32

-- | A constant.  Always written as @unit >>> scribe c@: the constant-word jets
-- only apply to constants whose input type is @()@, and a 256-bit constant
-- built from combinators at another input type costs tens of WU.
konst :: (Core term, TyC a, TyC b) => b -> term a b
konst c = unit >>> scribe c

-- | 1 when the optional value is present.
isSome :: (Core term, TyC a) => term (S a) Bit
isSome = iden &&& unit >>> match false true

-- | An expression that always fails.
failure :: (Assert term, TyC a, TyC b) => term a b
failure = assert (injl unit)

-- | Length in bytes of a 'Buffer511' (0 to 511), as a 16 bit word.
buf511Len :: Core term => term (Buffer511 Word8) Word16
buf511Len = hi &&& lo
 where
  f8 = take isSome
  f7 = drop (take isSome)
  f6 = drop (drop (take isSome))
  f5 = drop (drop (drop (take isSome)))
  f4 = drop (drop (drop (drop (take isSome))))
  f3 = drop (drop (drop (drop (drop (take isSome)))))
  f2 = drop (drop (drop (drop (drop (drop (take isSome))))))
  f1 = drop (drop (drop (drop (drop (drop (drop (take isSome)))))))
  f0 = drop (drop (drop (drop (drop (drop (drop (drop isSome)))))))
  z = false
  hi = ((z &&& z) &&& (z &&& z)) &&& ((z &&& z) &&& (z &&& f8))
  lo = ((f7 &&& f6) &&& (f5 &&& f4)) &&& ((f3 &&& f2) &&& (f1 &&& f0))

-- | Length in bytes of a 'Buffer63' (0 to 63), as a byte.
buf63Len :: Core term => term (Buffer63 Word8) Word8
buf63Len = ((false &&& false) &&& (f5 &&& f4)) &&& ((f3 &&& f2) &&& (f1 &&& f0))
 where
  f5 = take isSome
  f4 = drop (take isSome)
  f3 = drop (drop (take isSome))
  f2 = drop (drop (drop (take isSome)))
  f1 = drop (drop (drop (drop (take isSome))))
  f0 = drop (drop (drop (drop (drop isSome))))

-- | Append a Bitcoin CompactSize encoding of a length below 512.
ctxAddCompactSize511 :: Assert term => term (Ctx8, Word16) Ctx8
ctxAddCompactSize511 = (drop (iden &&& konst (toWord16 253) >>> Arith.lt word16)) &&& iden >>> cond small big
 where
  small = oh &&& iih >>> ctx8Add1
  big = ((oh &&& konst (toWord8 0xfd)) >>> ctx8Add1) &&& drop bswap16 >>> ctx8Add2

-- | Append a CompactSize length prefix followed by the bytes of the buffer (Bitcoin's @ser_string@).
ctxAddVarString511 :: Assert term => term (Ctx8, Buffer511 Word8) Ctx8
ctxAddVarString511 = (oh &&& drop buf511Len >>> ctxAddCompactSize511) &&& ih >>> ctx8AddBuffer511

-- | Append a 32 bit word in little endian order.
ctxAddLE32 :: Assert term => term (Ctx8, Word32) Ctx8
ctxAddLE32 = oh &&& drop bswap32 >>> ctx8Add4

-- | Append a 64 bit word in little endian order.
ctxAddLE64 :: Assert term => term (Ctx8, Word64) Ctx8
ctxAddLE64 = oh &&& drop bswap64 >>> ctx8Add8

-- | SHA-256 of the bytes in a buffer.
sha256Buffer511 :: Assert term => term (Buffer511 Word8) Word256
sha256Buffer511 = (unit >>> ctx8Init) &&& iden >>> ctx8AddBuffer511 >>> ctx8Finalize

ctxFinalizeHash :: Assert term => term Ctx8 Word256
ctxFinalizeHash = ctx8Finalize

-- Haskell-side value helpers ------------------------------------------------

w8 :: Integer -> Word8
w8 = toWord8
w16 :: Integer -> Word16
w16 = toWord16
w32 :: Integer -> Word32
w32 = toWord32
w64 :: Integer -> Word64
w64 = toWord64
w256 :: Integer -> Word256
w256 = toWord256

w256FromBytes :: BS.ByteString -> Word256
w256FromBytes = toWord256 . BS.foldl' (\a b -> a `shiftL` 8 + toInteger b) 0

w256ToBytes :: Word256 -> BS.ByteString
w256ToBytes w = BS.pack [ fromIntegral (x `shiftR` (8 * i)) | i <- [31, 30 .. 0] ]
 where x = fromWord256 w

buffer511FromBytes :: BS.ByteString -> Buffer511 Word8
buffer511FromBytes bs
  | BS.length bs > 511 = error "buffer511FromBytes: too long"
  | otherwise = fst (bufferFill buffer511 (map (toWord8 . toInteger) (BS.unpack bs)))

buffer63FromBytes :: BS.ByteString -> Buffer63 Word8
buffer63FromBytes bs
  | BS.length bs > 63 = error "buffer63FromBytes: too long"
  | otherwise = fst (bufferFill buffer63 (map (toWord8 . toInteger) (BS.unpack bs)))
