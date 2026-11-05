{-# LANGUAGE GADTs,ScopedTypeVariables #-}
-- | Full bounded SipHash-2-4, including tail and length finalization. Source:
-- Aumasson/Bernstein reference, pinned in vendor-specs/transport-crypto.
-- BIP152 and BIP158 consume the unsigned64 result with little-endian keys.
module JetDiscovery.Lib.SipHash (sipHash24,sipRound,SipState) where
import Prelude hiding (drop,take)
import Simplicity.Term.Core
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes

type SipState=((Word64,Word64),(Word64,Word64))
mk4 :: (Core t,TyC a,TyC x) => [t x a] -> t x ((a,a),(a,a))
mk4 [a,b,c,d]=(a&&&b)&&&(c&&&d)
mk4 _=error "SipHash.mk4"
a,b,c,d :: Core t => t SipState Word64
a=ooh;b=oih;c=ioh;d=iih
add,xor64 :: (Assert t,TyC x) => t x Word64 -> t x Word64 -> t x Word64
add x y=(x&&&y)>>>A.add word64>>>ih
xor64 x y=(x&&&y)>>>W.bitwise_xor word64
rot :: Core t => Integer -> t Word64 Word64
rot n=(konst(w8 n)&&&iden)>>>W.left_rotate word8 word64
sipRound :: Assert t => t SipState SipState
sipRound=first>>>second
 where
  first=mk4 [add a b>>>rot 32,xor64(b>>>rot 13)(add a b),add c d,xor64(d>>>rot 16)(add c d)]
  second=mk4 [add a d,xor64(b>>>rot 17)(add c b),add c b>>>rot 32,xor64(d>>>rot 21)(add a d)]

absorb :: Assert t => t (SipState,Word64) SipState
absorb=(mk4[take a,take b,take c,xor64(take d)ih]&&&ih)
 >>>(take(sipRound>>>sipRound)&&&ih)
 >>>mk4[xor64(take a)ih,take b,take c,take d]

consume :: (Core t,TyC state,TyC chunk,TyC rest)
 => t (state,chunk) state -> t (state,(S chunk,rest)) (state,rest)
consume body=(ioh&&&(oh&&&iih))>>>match ih ((((ioh&&&oh)>>>body)&&&iih))
consumeLast :: (Core t,TyC state,TyC chunk)
 => t (state,chunk) state -> t (state,S chunk) state
consumeLast body=(ih&&&oh)>>>match ih ((ih&&&oh)>>>body)
foldWords :: (Assert t,TyC v) => Vector Word64 v -> t (SipState,v) SipState
foldWords SingleV=(oh&&&(ih>>>bswap64))>>>absorb
foldWords (DoubleV v)=((oh&&&ioh)>>>foldWords v)&&&iih>>>foldWords v

type Tail=(Word64,Word8)
appendTail :: forall t chunk. (Assert t,TyC chunk)
 => Integer -> t chunk Word64 -> t (Tail,chunk) Tail
appendTail n little=(merged&&&((oih&&&konst(w8 n))>>>A.add word8>>>ih))
 where
  shift=((oih&&&konst(w8 8))>>>A.multiply word8>>>ih)
  shifted=(shift&&&(ih>>>little))>>>W.left_shift word8 word64
  merged=(ooh&&&shifted)>>>W.bitwise_or word64
tail7 :: Assert t => t (Buffer7 Word8) Word64
tail7=((konst(w64 0)&&&konst(w8 0))&&&iden)
 >>>consume(appendTail 4 ((konst(w32 0)&&&(iden>>>bswap32))))
 >>>consume(appendTail 2 (konst(w32 0)&&&(konst(w16 0)&&&(iden>>>bswap16))))
 >>>consumeLast(appendTail 1 (konst(w32 0)&&&(konst(w16 0)&&&(konst(w8 0)&&&iden))))>>>oh

sipHash24 :: Assert t => t ((Word64,Word64),Buffer511 Word8) Word64
sipHash24=((start>>>blocks)&&&(ih>>>buf511Len>>>ih))
 >>>(ooh&&&(((oih>>>tail7)&&&(ih>>>lengthWord))>>>W.bitwise_or word64))
 >>>absorb>>>mk4[a,b,(c&&&konst(w64 255))>>>W.bitwise_xor word64,d]
 >>>sipRound>>>sipRound>>>sipRound>>>sipRound
 >>>xor64(xor64 a b)(xor64 c d)
 where
  start=mk4[(ooh&&&konst(w64 0x736f6d6570736575))>>>W.bitwise_xor word64,
            (oih&&&konst(w64 0x646f72616e646f6d))>>>W.bitwise_xor word64,
            (ooh&&&konst(w64 0x6c7967656e657261))>>>W.bitwise_xor word64,
            (oih&&&konst(w64 0x7465646279746573))>>>W.bitwise_xor word64]&&&ih
  blocks=consume(foldWords vector32)>>>consume(foldWords vector16)
    >>>consume(foldWords vector8)>>>consume(foldWords vector4)
    >>>consume(foldWords vector2)>>>consume(foldWords vector1)
  lengthWord=((iden&&&konst(w8 0))&&&konst(w16 0))&&&konst(w32 0)
