{-# LANGUAGE GADTs,RankNTypes,ScopedTypeVariables #-}
-- | Complete bounded SHAKE256-2000 sponge:0..511 input bytes,250 output bytes.
-- Correct FIPS202 domain/padding, up to4absorbs and2squeeze blocks.
module JetDiscovery.Corpus.Shake256(entries,shakeT,Output250,Message) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.List as L
import Data.Bits(testBit)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Bitcoin.Term(Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import qualified Simplicity.Ty.Word as Ty
import JetDiscovery.Corpus.Hashes(keccakF)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Shake256 as R

type Message=(Word16,Word4096)
-- Exactly250bytes; no arbitrary extra output/witness padding.
type Output250=(Word1024,(Word512,(Word256,(Word128,(Word64,Word16)))))
type State=Vector32 Word64
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t(a,a)b
pick True=drop
pick False=take
byte :: Core t => Int -> t Word4096 Word8
byte i=pick(testBit i 8)(pick(testBit i 7)(pick(testBit i 6)(pick(testBit i 5)(pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))))))))
lane :: Core t => Int -> t State Word64
lane i=pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))))
byte64 :: Core t => Int -> t Word64 Word8
byte64 i=pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))
mk :: (Core t,TyC a) => Ty.Vector Word8 v -> [t a Word8] -> t a v
mk SingleV[x]=x
mk(DoubleV v)xs=mk v(P.take n xs)&&&mk v(P.drop n xs)where n=vectorSize v
mk _ _=error "SHAKE fixed byte packing"
mk8 :: (Core t,TyC a,TyC b) => [t a b] -> t a(Vector8 b)
mk8[a,b,c,d,e,f,g,h]=((a&&&b)&&&(c&&&d))&&&((e&&&f)&&&(g&&&h))
mk8 _=error "SHAKE mk8"
mk32 :: (Core t,TyC a,TyC b) => [t a b] -> t a(Vector32 b)
mk32 xs=(mk8(P.take 8 xs)&&&mk8(P.take 8(P.drop 8 xs)))&&&(mk8(P.take 8(P.drop 16 xs))&&&mk8(P.drop 24 xs))
{-# NOINLINE permutationWrapped #-}
permutationWrapped :: J.WrappedSimplicity State State
permutationWrapped=J.jetSubst keccakF
permutation :: Simplicity t => t State State
permutation=J.unwrap permutationWrapped
k16 :: (Core t,TyC a) => Integer -> t a Word16
k16=konst.w16
-- Each logical input enters once. All header/data reuse below is projection.
shakeT :: forall t. Simplicity t => t Message Output250
shakeT=(canonical&&&iden)>>>ih>>>(iden&&&konst(toWord word2048 0))>>>
 L.foldl'(>>>)iden[block b|b<-[0..3]]>>>ih>>>(iden&&&permutation)>>>output
 where
  size=oh
  canonical=( ((size&&&k16 511)>>>A.le word16>>>verify)&&&
    L.foldl'(\acc i->(acc&&&checkByte i)>>>unit)unit[0..511])>>>unit
  checkByte i=(((k16(toInteger i)&&&size)>>>A.lt word16)&&&iden)>>>cond unit
    (((ih>>>byte i)&&&konst(w8 0))>>>eq>>>verify)
  block b=(active&&&iden)>>>cond absorb iden
   where
    start=136*b
    active=(k16(toInteger start)&&&ooh)>>>A.le word16
    msgByte i | i>=512=konst(w8 0)
              | otherwise=take(drop(byte i))
    delimiter i=(((ooh&&&k16(toInteger i))>>>eq)&&&unit)>>>cond(konst(w8 0x1f))(konst(w8 0))
    endPad i | i/=start+135=konst(w8 0)
             | otherwise=(((ooh&&&k16(toInteger(start+136)))>>>A.lt word16)&&&unit)>>>cond(konst(w8 0x80))(konst(w8 0))
    padded i=(((msgByte i&&&delimiter i)>>>W.bitwise_or word8)&&&endPad i)>>>W.bitwise_or word8
    laneIn i | i>=17=drop(lane i)
             | otherwise=(drop(lane i)&&&mk vector8[padded(start+8*i+j)|j<-[7,6..0]])>>>W.bitwise_xor word64
    absorb=oh&&&(mk32[laneIn i|i<-[0..31]]>>>permutation)
  resultByte i | i<136=take(lane(i`div`8)>>>bswap64>>>byte64(i`mod`8))
               | otherwise=drop(lane((i-136)`div`8)>>>bswap64>>>byte64((i-136)`mod`8))
  pack :: Ty.Vector Word8 v -> Int -> t(State,State)v
  pack n start=mk n[resultByte i|i<-[start..start+vectorSize n-1]]
  output=pack vector128 0&&&(pack vector64 128&&&(pack vector32 192&&&(pack vector16 224&&&(pack vector8 240&&&pack vector2 248))))

type Input=(Message,Output250)
kernel :: Simplicity t => t Input ()
kernel=((oh>>>shakeT)&&&ih)>>>eq>>>verify
integer=BS.foldl'(\a b->a*256+toInteger b)0
message b | BS.length b<=512=(w16(toInteger(BS.length b)),toWord word4096(integer(b<>BS.replicate(512-BS.length b)0)))
          | otherwise=error "SHAKE message bound"
expected b | BS.length b/=250=error "SHAKE output requires250bytes"
           | otherwise=(toWord word1024(part 0 128),(toWord word512(part 128 64),(w256(part 192 32),(toWord word128(part 224 16),(w64(part 240 8),w16(part 248 2))))))
 where part i n=integer(BS.take n(BS.drop i b))
encode b=case R.shake250 b of Just out->(message b,expected out);_->error "SHAKE reference input out of bound"
env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
split []=[[]]
split('\t':xs)=[]:split xs
split(x:xs)=case split xs of a:as->(x:a):as;_->error "SHAKE TSV split"
entries :: IO [Entry]
entries=do
 rows<-map(map(init.tail).split).tail.lines <$>readFile "vendor-specs/crypto-families/shake256-kat250.tsv"
 let official=[Vector("NIST complete2000bit"++source++":"++i)env(message(unhex msg),expected(unhex out))Accept|[source,i,msg,out]<-rows]
 if length official/=6 then error "SHAKE expected all6complete supported NISTcases"else pure()
 let pattern n=BS.pack[fromIntegral(i`mod`251)|i<-[0..n-1]]
     boundary=[Vector("derived rate/input boundary"++show n)env(encode(pattern n))Accept|n<-[0,1,135,136,137,271,272,511]]
     (empty,emptyOutput)=encode BS.empty
     badPadding=(w16 0,toWord word4096(2^(4096-8)))
     badOutput=let(a,b)=emptyOutput in(toWord word1024(fromWord word1024 a+1),b)
 pure[Entry "crypto-shake256-xof" "Full bounded SHAKE256-2000 sponge with variable absorption and two squeeze blocks"
  "FIPS202 sections6.2/algorithm8; official NIST CAVP SHAKE256VariableOut byte-oriented vectors, source packet crypto-families"
  PostQuantum(Upstream "all6complete supported NIST2000bit outputs; additional derived empty/rate/input boundaries and canonical padding/length/output negatives")
  ["one SHAKE XOF family, not an additional Keccak permutation or a full ML-DSA/Falcon verifier; dependencies motivate Bitcoin PQ authorization",
   "input0..511bytes, fixed250-byte output, rate136, domain0x1f, correct0x9f delimiter/end overlap; up to4absorb permutations and exactly2squeeze blocks",
   "raw512-byte message field is strictly zero after the authenticated length; all witness bits are real encoded data for budget analysis, with no padding-based feasibility claim",
   "one aggregate witness feeds the pure kernel; expected output is exactly250bytes and all bytes are checked"]
  (boundProgram kernel)(official++boundary++
   [Vector "length512 exceeds511" env ((w16 512,snd empty),emptyOutput)Reject,
    Vector "nonzero unused input byte" env (badPadding,emptyOutput)Reject,
    Vector "same-CMR output corruption" env (empty,badOutput)Reject])]
