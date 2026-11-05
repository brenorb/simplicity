{-# LANGUAGE ScopedTypeVariables #-}
-- | RFC8439 complete20-round block function. Words are numerical little-endian
-- key/nonce/output words; byte serialization is an explicitly separate codec.
module JetDiscovery.Lib.ChaCha20 (chacha20Block,quarterRound,Parameters) where
import Prelude hiding (take,drop)
import qualified Prelude as P
import Data.Bits(testBit)
import Simplicity.Term.Core
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes

type Parameters=(Vector8 Word32,(Word32,(Word32,(Word32,Word32))))
type Four=((Word32,Word32),(Word32,Word32))
mk4 :: (Core t,TyC a,TyC x) => [t x a] -> t x ((a,a),(a,a))
mk4[a,b,c,d]=(a&&&b)&&&(c&&&d)
mk4 _=error "ChaCha20.mk4"
mk8 xs=mk4(P.take 4 xs)&&&mk4(P.drop 4 xs)
mk16 xs=mk8(P.take 8 xs)&&&mk8(P.drop 8 xs)
pick :: (Core t,TyC a,TyC c) => Bool -> t a c -> t(a,a)c
pick False=take
pick True=drop
at4 :: (Core t,TyC a) => Int -> t((a,a),(a,a))a
at4 n=pick(testBit n 1)(pick(testBit n 0)iden)
at8 :: (Core t,TyC a) => Int -> t(Vector8 a)a
at8 n=pick(testBit n 2)(at4 n)
at16 :: (Core t,TyC a) => Int -> t(Vector16 a)a
at16 n=pick(testBit n 3)(at8 n)
plus :: (Assert t,TyC x) => t x Word32 -> t x Word32 -> t x Word32
plus a b=(a&&&b)>>>A.add word32>>>ih
xorRot :: (Core t,TyC x) => Integer -> t x Word32 -> t x Word32 -> t x Word32
xorRot n a b=(konst(w8 n)&&&((a&&&b)>>>W.bitwise_xor word32))>>>W.left_rotate word8 word32
quarterRound :: Assert t => t Four Four
quarterRound=ad 16>>>cb 12>>>ad 8>>>cb 7
 where
  ad n=mk4[plus ooh oih,oih,ioh,xorRot n iih(plus ooh oih)]
  cb n=mk4[ooh,xorRot n oih(plus ioh iih),plus ioh iih,iih]
half :: Assert t => [[Int]] -> t(Vector16 Word32)(Vector16 Word32)
half lanes=mk4[mk4(map at16 lane)>>>quarterRound|lane<-lanes]>>>mk16[place i|i<-[0..15]]
 where
  place i=case[(j,k)|(j,lane)<-zip[0..]lanes,(k,v)<-zip[0..]lane,v==i]of
    [(j,k)]->at4 j>>>at4 k
    _->error "ChaCha20 lane partition"
chacha20Block :: forall t. Assert t => t Parameters(Vector16 Word32)
chacha20Block=(initial&&&(initial>>>rounds))>>>mk16[plus(take(at16 i))(drop(at16 i))|i<-[0..15]]
 where
  initial :: t Parameters(Vector16 Word32)
  initial=mk16(map(konst.w32)[0x61707865,0x3320646e,0x79622d32,0x6b206574]
    ++[take(at8 i)|i<-[0..7]]++[ioh,iioh,drop(drop(drop oh)),drop(drop(drop ih))])
  double=half[[0,4,8,12],[1,5,9,13],[2,6,10,14],[3,7,11,15]]
    >>>half[[0,5,10,15],[1,6,11,12],[2,7,8,13],[3,4,9,14]]
  rounds=P.foldr(>>>)iden(P.replicate 10 double)
