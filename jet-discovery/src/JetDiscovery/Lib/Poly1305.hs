{-# LANGUAGE GADTs,ScopedTypeVariables #-}
-- | Complete bounded RFC8439 Poly1305 with clamping, partial blocks, canonical
-- reduction mod2^130-5 and final addition mod2^128. No arithmetic witness hints.
module JetDiscovery.Lib.Poly1305 (poly1305) where
import Prelude hiding(take,drop,not)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Word as W
import qualified Simplicity.Programs.Arith as A
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes

type State=(Word256,Word256) -- clamped r, canonical accumulator
type Tail=(Word128,Word8)
bswap128 :: Core t => t Word128 Word128
bswap128=(ih>>>bswap64)&&&(oh>>>bswap64)
consume :: (Core t,TyC s,TyC chunk,TyC rest)
 => t(s,chunk)s -> t(s,(S chunk,rest))(s,rest)
consume body=(ioh&&&(oh&&&iih))>>>match ih (((ioh&&&oh)>>>body)&&&iih)
consumeLast :: (Core t,TyC s,TyC chunk) => t(s,chunk)s -> t(s,S chunk)s
consumeLast body=(ih&&&oh)>>>match ih ((ih&&&oh)>>>body)

-- Two folds suffice for every256-bit input: the first result is below2^131,
-- the second at most2^130+4, so one final subtraction canonicalizes it.
reduce :: Assert t => t Word256 Word256
reduce=fold130>>>fold130>>>canon
 where
  low=(iden&&&konst(w256(2^(130::Int)-1)))>>>W.bitwise_and word256
  high=(konst(w8 130)&&&iden)>>>W.right_shift word8 word256
  times5=(iden&&&konst(w256 5))>>>A.multiply word256>>>ih
  fold130=(low&&&(high>>>times5))>>>A.add word256>>>ih
  canon=(iden&&&((iden&&&konst(w256(2^(130::Int)-5)))>>>A.subtract word256))
    >>>(ioh&&&(oh&&&iih))>>>cond oh ih

step :: forall t. Assert t => t(State,Word256)State
step=ooh&&&productReduced
 where
  total=(oih&&&ih)>>>A.add word256>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  productReduced=(total&&&ooh)>>>A.multiply word256
    >>>((((oh&&&konst(w256 0))>>>eq>>>verify)&&&ih)>>>ih)>>>reduce
fullBlock :: Assert t => t(State,Word128)State
fullBlock=(oh&&&(konst(toWord128 1)&&&(ih>>>bswap128)))>>>step
foldBlocks :: (Assert t,TyC v) => Vector Word128 v -> t(State,v)State
foldBlocks SingleV=fullBlock
foldBlocks(DoubleV v)=((oh&&&ioh)>>>foldBlocks v)&&&iih>>>foldBlocks v

appendTail :: forall t chunk. (Assert t,TyC chunk)
 => Integer -> t chunk Word128 -> t(Tail,chunk)Tail
appendTail n little=(((ooh&&&shifted)>>>W.bitwise_or word128)&&&((oih&&&konst(w8 n))>>>A.add word8>>>ih))
 where
  amount=(oih&&&konst(w8 8))>>>A.multiply word8>>>ih
  shifted=(amount&&&(ih>>>little))>>>W.left_shift word8 word128
tail15 :: Assert t => t(Buffer15 Word8)Tail
tail15=((konst(toWord128 0)&&&konst(w8 0))&&&iden)
 >>>consume(appendTail 8 (konst(w64 0)&&&(iden>>>bswap64)))
 >>>consume(appendTail 4 (konst(w64 0)&&&(konst(w32 0)&&&(iden>>>bswap32))))
 >>>consume(appendTail 2 (konst(w64 0)&&&(konst(w32 0)&&&(konst(w16 0)&&&(iden>>>bswap16)))))
 >>>consumeLast(appendTail 1 (konst(w64 0)&&&(konst(w32 0)&&&(konst(w16 0)&&&(konst(w8 0)&&&iden)))))
partial :: Assert t => t(State,Buffer15 Word8)State
partial=(oh&&&(ih>>>tail15))>>>(((iih&&&konst(w8 0))>>>eq)&&&iden)>>>cond oh append
 where
  amount=(iih&&&konst(w8 8))>>>A.multiply word8>>>ih
  marker=(amount&&&konst(w256 1))>>>W.left_shift word8 word256
  encoded=((konst(toWord128 0)&&&ioh)&&&marker)>>>W.bitwise_or word256
  append=(oh&&&encoded)>>>step

poly1305 :: Assert t => t(Word256,Buffer511 Word8)Word128
poly1305=((start>>>blocks>>>partial)&&&(oih>>>bswap128))
 >>>((oih>>>ih)&&&ih)>>>A.add word128>>>ih
 where
  clamped=(ooh>>>bswap128)&&&konst(toWord128 0x0ffffffc0ffffffc0ffffffc0fffffff)>>>W.bitwise_and word128
  start=(((konst(toWord128 0)&&&clamped)&&&konst(w256 0))&&&ih)
  blocks=consume(foldBlocks vector16)>>>consume(foldBlocks vector8)
    >>>consume(foldBlocks vector4)>>>consume(foldBlocks vector2)>>>consume(foldBlocks vector1)
