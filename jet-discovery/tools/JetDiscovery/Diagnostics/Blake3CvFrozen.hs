-- Historical own source for exact CV API equivalence only.
{-# LANGUAGE GADTs,RankNTypes,ScopedTypeVariables #-}
-- | Complete unkeyed BLAKE3-256, input0..2048bytes, with real two-chunk parent.
module JetDiscovery.Diagnostics.Blake3CvFrozen(entries,hashT,compressT,compressChainingT,canonicalBlockT,Message) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.List as L
import Data.Bits(testBit,shiftR)
import Simplicity.Term.Core
import Simplicity.Programs.Bit hiding(xor)
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Bitcoin.Term(Simplicity,Primitive)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import qualified Simplicity.Ty.Word as Ty
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Blake3 as R

type CV=Vector8 Word32
type Block=Vector16 Word32
type Message=Vector32 Word512
type Plain=(Word16,Message)
type Compression=(CV,(Block,(Word64,(Word32,Word32))))
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t(a,a)b
pick True=drop
pick False=take
at4 :: Core t => Int -> t(Vector4 Word32)Word32
at4 i=pick(testBit i 1)(pick(testBit i 0)iden)
at8 :: Core t => Int -> t CV Word32
at8 i=pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))
at16 :: Core t => Int -> t Block Word32
at16 i=pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden)))
byte512 :: Core t => Int -> t Word512 Word8
byte512 i=pick(testBit i 5)(pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden)))))
mk :: (Core t,TyC a) => Ty.Vector Word32 v -> [t a Word32] -> t a v
mk SingleV[x]=x
mk(DoubleV v)xs=mk v(P.take n xs)&&&mk v(P.drop n xs)where n=vectorSize v
mk _ _=error "BLAKE3 fixed word packing"
k32 :: (Core t,TyC a) => Integer -> t a Word32
k32=konst.w32
k16 :: (Core t,TyC a) => Integer -> t a Word16
k16=konst.w16
add a b=(a&&&b)>>>A.add word32>>>ih
xor a b=(a&&&b)>>>W.bitwise_xor word32
rotate n=konst(w8 n)&&&iden>>>W.right_rotate word8 word32
p3 t=take(take(take t))
p4 t=take(p3 t)
-- BLAKE3 G on four state words and two message words. Each intermediate enters
-- its later two uses once as actual data, not a repeated expression/hint.
mixRef :: Assert t => t(Vector4 Word32,(Word32,Word32))(Vector4 Word32)
mixRef=s1>>>s2>>>s3>>>s4>>>s5>>>s6>>>s7>>>s8>>>((p3 ih&&&ih)&&&(take ih&&&take(take ih)))
 where
  a=take ooh;b=take oih;c=take ioh;d=take iih;x=ioh;y=iih
  s1=iden&&&add(add a b)x
  s2=iden&&&(xor(take d)ih>>>rotate 16)
  s3=iden&&&add(take(take c))ih
  s4=iden&&&(xor(p3 b)ih>>>rotate 12)
  s5=iden&&&add(add(p3 ih)ih)(p4 y)
  s6=iden&&&(xor(p3 ih)ih>>>rotate 8)
  s7=iden&&&add(p3 ih)ih
  s8=iden&&&(xor(p3 ih)ih>>>rotate 7)
{-# NOINLINE mixWrapped #-}
mixWrapped :: J.WrappedSimplicity (Vector4 Word32,(Word32,Word32))(Vector4 Word32)
mixWrapped=J.jetSubst mixRef
mixT :: Simplicity t => t(Vector4 Word32,(Word32,Word32))(Vector4 Word32)
mixT=J.unwrap mixWrapped

compressRef :: Simplicity t => t Compression Block
compressRef=setup>>>L.foldl'(>>>)iden[step schedule i points|schedule<-schedules,(i,points)<-zip[0..]groups]>>>output
 where
  cv=oh;msg=ioh;counter=drop(drop oh);len=drop(drop(drop oh));flags=drop(drop(drop ih))
  initial=mk vector16([cv>>>at8 i|i<-[0..7]]++[k32(toInteger v)|v<-P.take 4 R.iv]++[counter>>>ih,counter>>>oh,len,flags])
  setup=cv&&&(msg&&&initial)
  permutation=[2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8]
  schedules=P.take 7(iterate(\s->map(s!!)permutation)[0..15])
  groups=[(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]
  step schedule i(a,b,c,d)=(iden&&&new4)>>>(take oh&&&(take ioh&&&mk vector16[newWord j|j<-[0..15]]))
   where
    new4=(mk vector4[iih>>>at16 j|j<-[a,b,c,d]]&&&((ioh>>>at16(schedule!!(2*i)))&&&(ioh>>>at16(schedule!!(2*i+1)))))>>>mixT
    newWord j=case L.elemIndex j[a,b,c,d]of Just k->drop(at4 k);Nothing->take(iih>>>at16 j)
  output=mk vector16([xor(iih>>>at16 i)(iih>>>at16(i+8))|i<-[0..7]]++[xor(iih>>>at16(i+8))(oh>>>at8 i)|i<-[0..7]])
{-# NOINLINE compressionWrapped #-}
compressionWrapped :: J.WrappedSimplicity Compression Block
compressionWrapped=J.jetSubst compressRef
compressT :: Simplicity t => t Compression Block
compressT=J.unwrap compressionWrapped
-- The bounded32-byte hash requires only the first8compression output words.
-- Compute that exact output directly: the original CV is already in the
-- initial state and need not survive56G steps solely for the unused second
-- half of the extended-output compression function. Public compressT retains
-- the full16word reference for independent primitive checks.
compressChainingRef :: Simplicity t => t Compression CV
compressChainingRef=setup>>>L.foldl'(>>>)iden[step schedule i points|schedule<-schedules,(i,points)<-zip[0..]groups]>>>
 mk vector8[xor(ih>>>at16 i)(ih>>>at16(i+8))|i<-[0..7]]
 where
  cv=oh;msg=ioh;counter=drop(drop oh);len=drop(drop(drop oh));flags=drop(drop(drop ih))
  initial=mk vector16([cv>>>at8 i|i<-[0..7]]++[k32(toInteger v)|v<-P.take 4 R.iv]++[counter>>>ih,counter>>>oh,len,flags])
  setup=msg&&&initial
  permutation=[2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8]
  schedules=P.take 7(iterate(\s->map(s!!)permutation)[0..15])
  groups=[(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]
  step schedule i(a,b,c,d)=(iden&&&new4)>>>(take oh&&&mk vector16[newWord j|j<-[0..15]])
   where
    new4=(mk vector4[ih>>>at16 j|j<-[a,b,c,d]]&&&((oh>>>at16(schedule!!(2*i)))&&&(oh>>>at16(schedule!!(2*i+1)))))>>>mixT
    newWord j=case L.elemIndex j[a,b,c,d]of Just k->drop(at4 k);Nothing->take(ih>>>at16 j)
{-# NOINLINE chainingWrapped #-}
chainingWrapped :: J.WrappedSimplicity Compression CV
chainingWrapped=J.jetSubst compressChainingRef
compressChainingT :: Simplicity t => t Compression CV
compressChainingT=J.unwrap chainingWrapped
ivT :: (Core t,TyC a) => t a CV
ivT=mk vector8[k32(toInteger x)|x<-R.iv]
digestT :: Core t => t CV Word256
digestT=mk vector8[at8 i>>>bswap32|i<-[0..7]]
{-# NOINLINE zeroBlockWrapped #-}
zeroBlockWrapped :: J.WrappedSimplicity Word512 ()
zeroBlockWrapped=J.jetSubst((iden&&&konst(toWord word512 0))>>>eq>>>verify)
zeroBlockT :: Simplicity t => t Word512 ()
zeroBlockT=J.unwrap zeroBlockWrapped
-- Drop the valid prefix by a BYTE shift; every remaining byte must be zero.
-- This is the same canonical padding relation as64separate indexed checks,
-- with one small shared kernel instead of retaining the header at every byte.
canonicalBlockRef :: Simplicity t => t(Word8,Word512)()
canonicalBlockRef=(((oh&&&konst(w8 64))>>>A.le word8>>>verify)&&&iden)>>>ih>>>
 (konst(w8 0)&&&iden)>>>W.left_shift_with word8 vector64>>>zeroBlockT
{-# NOINLINE canonicalBlockWrapped #-}
canonicalBlockWrapped :: J.WrappedSimplicity(Word8,Word512)()
canonicalBlockWrapped=J.jetSubst canonicalBlockRef
canonicalBlockT :: Simplicity t => t(Word8,Word512)()
canonicalBlockT=J.unwrap canonicalBlockWrapped

-- Consume each block once and discard it. The recursive split shrinks the
-- live context instead of carrying the whole2048-byte input through every G.
foldChunk :: Simplicity t => Int -> Int -> Ty.Vector Word512 v -> t(Word16,(v,CV))(Word16,CV)
foldChunk chunk index SingleV=((padding&&&iden)>>>ih)>>>(oh&&&((active&&&iden)>>>cond calculate iih))
 where
  start=1024*chunk+64*index;end=start+64
  full=(k16(toInteger end)&&&oh)>>>A.le word16
  empty=(oh&&&k16(toInteger start))>>>A.le word16
  padding=(full&&&iden)>>>cond unit((empty&&&iden)>>>cond zero partial)
  zero=ioh>>>zeroBlockT
  partial=((short>>>ih)&&&ioh)>>>canonicalBlockT
  active=if chunk==0&&index==0 then true else(k16(toInteger start)&&&oh)>>>A.lt word16
  isFinal=if index==15 then true else(oh&&&k16(toInteger end))>>>A.le word16
  base=if index==0 then 1 else 0
  finalFlags | chunk==1=k32(base+2)
             | otherwise=(((oh&&&k16 1024)>>>A.le word16)&&&unit)>>>cond(k32(base+10))(k32(base+2))
  flags=(isFinal&&&iden)>>>cond finalFlags(k32 base)
  short=(oh&&&k16(toInteger start))>>>A.subtract word16>>>ih
  blockLen=(full&&&iden)>>>cond(k32 64)(konst(w16 0)&&&short)
  wordsT=ioh>>>mk vector16[at16 i>>>bswap32|i<-[0..15]]
  calculate=(iih&&&(wordsT&&&(konst(w64(toInteger chunk))&&&(blockLen&&&flags))))>>>compressChainingT
foldChunk chunk index(DoubleV v)=
 ((oh&&&(iooh&&&iih))&&&ioih)>>>
 (take(foldChunk chunk index v)&&&drop iden)>>>
 (ooh&&&(ih&&&oih))>>>foldChunk chunk(index+vectorSize v)v
zeroBlocks :: Simplicity t => Ty.Vector Word512 v -> t v ()
zeroBlocks SingleV=zeroBlockT
zeroBlocks(DoubleV v)=(take(zeroBlocks v)&&&drop(zeroBlocks v))>>>unit

hashT :: Simplicity t => t Plain Word256
hashT=(((oh&&&k16 2048)>>>A.le word16>>>verify)&&&iden)>>>ih>>>
 ((oh&&&(ioh&&&ivT))&&&iih)>>>(take(foldChunk 0 0 vector16)&&&drop iden)>>>
 ((((ooh&&&k16 1024)>>>A.le word16)&&&iden)>>>cond single twoChunks)
 where
  single=((drop(zeroBlocks vector16))&&&(oih>>>digestT))>>>ih
  twoChunks=(oih&&&(ooh&&&(ih&&&ivT)))>>>(oh&&&drop(foldChunk 1 0 vector16))>>>
    (ivT&&&((oh&&&iih)&&&(konst(w64 0)&&&(k32 64&&&k32 12))))>>>compressChainingT>>>digestT
type Input=(Plain,Word256)
kernel :: Simplicity t => t Input ()
kernel=((oh>>>hashT)&&&ih)>>>eq>>>verify
-- The complete2048-byte array is not carried through the typed compression
-- expression. Bind the shared length once; each independent block enters once
-- at its consuming stage and is checked and compressed through projections.
-- This is deliberately a legacy Prog: internal witnesses disallow prepared
-- kernels, and no repeated-witness identity assumption is needed.
unpackBlocks :: Ty.Vector Word512 v -> v -> [Word512]
unpackBlocks SingleV x=[x]
unpackBlocks(DoubleV v)(a,b)=unpackBlocks v a++unpackBlocks v b
program :: Input -> Prog
program ((size,raw),expected)=Prog complete
 where
  blocks=unpackBlocks vector32 raw
  complete :: forall t. (Simplicity t,Primitive t) => t () ()
  complete=witness size>>>(((iden&&&k16 2048)>>>A.le word16>>>verify)&&&iden)>>>ih>>>
   (iden&&&ivT)>>>L.foldl'(>>>)iden[consume 0 i(blocks!!i)|i<-[0..15]]>>>
   (ih&&&(oh&&&ivT))>>>L.foldl'(>>>)iden[oh&&&drop(consume 1 i(blocks!!(16+i)))|i<-[0..15]]>>>
   (((ioh&&&k16 1024)>>>A.le word16)&&&iden)>>>cond(oh>>>digestT)parent>>>
   (iden&&&witness expected)>>>eq>>>verify
  consume :: forall t. Simplicity t => Int -> Int -> Word512 -> t(Word16,CV)(Word16,CV)
  consume chunk i block=(oh&&&(witness block&&&ih))>>>foldChunk chunk i SingleV
  parent :: forall t. Simplicity t => t(CV,(Word16,CV))Word256
  parent=(ivT&&&((oh&&&iih)&&&(konst(w64 0)&&&(k32 64&&&k32 12))))>>>compressChainingT>>>digestT
integer=BS.foldl'(\a b->256*a+toInteger b)0
v4[a,b,c,d]=((a,b),(c,d))
v4 _=error "BLAKE3 v4"
v16 xs=v4[v4(P.take 4(P.drop i xs))|i<-[0,4,8,12]]
v32 xs=(v16(P.take 16 xs),v16(P.drop 16 xs))
message b | BS.length b<=2048=(w16(toInteger(BS.length b)),v32[toWord word512(integer(BS.take 64(BS.drop(64*i)padded)))|i<-[0..31]])
          | otherwise=error "BLAKE3 fixture exceeds2048bytes"
 where padded=b<>BS.replicate(2048-BS.length b)0
encode b=case R.hash256 b of Just h->(message b,w256FromBytes h);_->error "BLAKE3 reference input exceedsbound"
env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
split []=[[]]
split('\t':xs)=[]:split xs
split(x:xs)=case split xs of a:as->(x:a):as;_->error "BLAKE3 TSV split"
entries :: IO [Entry]
entries=do
 rows<-map(map(init.tail).split).tail.lines <$>readFile "vendor-specs/crypto-families/blake3-unkeyed-bounded.tsv"
 let official=[Vector("official unkeyed BLAKE3 case"++i++" bytes"++len)env(message(R.patternInput(read len)),w256FromBytes(unhex out))Accept|[i,len,out]<-rows]
 if length official/=19 then error "BLAKE3 expected all19 supported officialcases"else pure()
 let (empty,out)=encode BS.empty
     badPadding=(w16 0,snd(message(BS.singleton 1)))
     unmasked=R.compress R.iv(1:replicate 15 0)0 0 11
     unmaskedHash=BS.pack[fromIntegral(x`shiftR`(8*i))|x<-P.take 8 unmasked,i<-[0..3]]
 pure[Entry "crypto-blake3-tree-hash" "Complete bounded BLAKE3 unkeyed hash with chunk chaining and parent-root processing"
  "BLAKE3 specification pinnedac784c9f..., official repository/test_vectors f55849f8...; direct BitVM chunker source demand pinnedc620dbfa..."
  Eprint(Upstream "all19official unkeyed32byte cases with input<=2048bytes, including1023/1024/1025/2048; other modes/lengths fully inventoried and excluded")
  ["complete bounded hash component, not only a compression or a full BitVM bridge; one BLAKE3 counting family despite block/chunk/input variants",
   "input0..2048bytes,32byte default digest, exact7round compression,64byte blocks,1024byte chunks, counter/start/end/parent/root flags; two actual chunks at maximum bound",
   "all unused raw message bytes strictlyzero; shared length bound once, each independent64-byte block bound once and consumed/discarded; full encoded witness size is counted without padding-based budget claims",
   "unkeyed mode only; keyed/derive-key/XOF extensions are outside this profile and earn no extra application count"]
  program(official++
   [Vector "input length2049 exceedsbound" env ((w16 2049,snd empty),out)Reject,
    Vector "nonzero unused byte with matching unmasked compression output" env (badPadding,w256FromBytes unmaskedHash)Reject,
    Vector "same-CMR digest corruption" env (empty,w256(fromWord256 out+1))Reject])]
