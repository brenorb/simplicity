{-# LANGUAGE ScopedTypeVariables,RankNTypes #-}
-- | One Poseidon2 component family: full KoalaBear16 permutation, including
-- initial diffusion,8full/20partial rounds, both exact constant profiles.
module JetDiscovery.Corpus.Poseidon2 (entries,permutationT,State) where
import Prelude hiding(drop,take,not,and,or)
import qualified Data.List as L
import Data.Bits(testBit)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Bitcoin.Term(Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Poseidon2 as R
import qualified JetDiscovery.Ref.Poseidon2Constants as C

type State=Vector16 Word32
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t(a,a)b
pick True=drop
pick False=take
at :: Core t => Int -> t State Word32
at i=pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden)))
mk4 :: (Core t,TyC a,TyC b) => [t a b] -> t a(Vector4 b)
mk4[a,b,c,d]=(a&&&b)&&&(c&&&d)
mk4 _=error "Poseidon2 mk4"
mk16 :: (Core t,TyC a,TyC b) => [t a b] -> t a(Vector16 b)
mk16 xs=mk4[mk4(L.take 4(L.drop i xs))|i<-[0,4,8,12]]
k32 :: (Core t,TyC a) => Integer -> t a Word32
k32=konst.w32
-- All callers maintain canonical field values.2q<2^32, q^2<2^62.
canon :: Assert t => t Word32 Word32
canon=((iden&&&k32 R.q)>>>A.subtract word32)&&&iden>>>
 ((ooh&&&(ih&&&oih))>>>cond oh ih)
addRef :: Assert t => t(Word32,Word32)Word32
addRef=A.add word32>>>ih>>>canon
mulRef :: Assert t => t(Word32,Word32)Word32
mulRef=(A.multiply word32&&&konst(w64 R.q))>>>A.div_mod word64>>>ih>>>ih
{-# NOINLINE addWrapped #-}
addWrapped :: J.WrappedSimplicity (Word32,Word32) Word32
addWrapped=J.jetSubst addRef
{-# NOINLINE mulWrapped #-}
mulWrapped :: J.WrappedSimplicity (Word32,Word32) Word32
mulWrapped=J.jetSubst mulRef
-- Cache these monomorphic existing-jet frontends instead of rebuilding the
-- generic64-bit divider at every S-box/matrix coefficient. No new jet/cost.
addF :: Simplicity t => t(Word32,Word32)Word32
addF=J.unwrap addWrapped
mulF :: Simplicity t => t(Word32,Word32)Word32
mulF=J.unwrap mulWrapped
{-# NOINLINE cubeWrapped #-}
cubeWrapped :: J.WrappedSimplicity Word32 Word32
cubeWrapped=J.jetSubst((iden&&&((iden&&&iden)>>>mulF))>>>mulF)
cube :: Simplicity t => t Word32 Word32
cube=J.unwrap cubeWrapped
add a b=(a&&&b)>>>addF
mul a b=(a&&&b)>>>mulF
sum4[a,b,c,d]=add(add a b)(add c d)
sum4 _=error "Poseidon2 sum4"
sum16 xs=sum4[sum4(L.take 4(L.drop i xs))|i<-[0,4,8,12]]

-- Optimized4x4 row sums, followed by the outer four-block circulant layer.
externalRef :: Simplicity t => t State State
externalRef=matrix4>>> (iden&&&mk4 columns)>>>mk16[add(take(at i))(drop(col(i`mod`4)))|i<-[0..15]]
 where
  twice x=add x x
  row b i=case i of
   0->sum4[twice(at b),add(twice(at(b+1)))(at(b+1)),at(b+2),at(b+3)]
   1->sum4[at b,twice(at(b+1)),add(twice(at(b+2)))(at(b+2)),at(b+3)]
   2->sum4[at b,at(b+1),twice(at(b+2)),add(twice(at(b+3)))(at(b+3))]
   _->sum4[add(twice(at b))(at b),at(b+1),at(b+2),twice(at(b+3))]
  matrix4=mk16[row b i|b<-[0,4,8,12],i<-[0..3]]
  columns=[sum4[at j|j<-[i,i+4..15]]|i<-[0..3]]
  col i=pick(testBit i 1)(pick(testBit i 0)iden)
internalRef :: Simplicity t => t State State
internalRef=(iden&&&sum16[at i|i<-[0..15]])>>>mk16[add ih(mul(take(at i))(k32(R.diagonal!!i)))|i<-[0..15]]
{-# NOINLINE externalWrapped #-}
externalWrapped :: J.WrappedSimplicity State State
externalWrapped=J.jetSubst externalRef
{-# NOINLINE internalWrapped #-}
internalWrapped :: J.WrappedSimplicity State State
internalWrapped=J.jetSubst internalRef
externalT,internalT :: Simplicity t => t State State
externalT=J.unwrap externalWrapped
internalT=J.unwrap internalWrapped

permutationT :: Simplicity t => t(Bit,State)State
permutationT=(oh&&&(ih>>>externalT))>>>
 L.foldl'(>>>)iden[full a b|(a,b)<-zip C.defaultInitial C.zirenInitial]>>>
 L.foldl'(>>>)iden[partial a b|(a,b)<-zip C.defaultInternal C.zirenInternal]>>>
 L.foldl'(>>>)iden[full a b|(a,b)<-zip C.defaultFinal C.zirenFinal]>>>ih
 where
  constant a b=(oh&&&unit)>>>cond(k32 b)(k32 a)
  full a b=(oh&&&mk16[(add(ih>>>at i)(constant(a!!i)(b!!i)))>>>cube|i<-[0..15]])>>>(oh&&&(ih>>>externalT))
  partial a b=(iden&&&((add(ih>>>at 0)(constant a b))>>>cube))>>>
    (ooh&&&(mk16(ih:[take(drop(at i))|i<-[1..15]])>>>internalT))
type Input=((Bit,State),State)
kernel :: Simplicity t => t Input ()
kernel=(canonical&&&(((oh>>>permutationT)&&&ih)>>>eq>>>verify))>>>unit
 where canonical=L.foldl'(\acc i->acc&&&(((oh>>>ih>>>at i)&&&k32 R.q)>>>A.lt word32>>>verify)>>>unit)unit[0..15]
v4[a,b,c,d]=((a,b),(c,d))
v4 _=error "Poseidon2 v4"
v16 xs=v4[v4(L.take 4(L.drop i xs))|i<-[0,4,8,12]]
value xs=v16(map w32 xs)
bit b=if b then Right()else Left()
encode(profile,xs)=case R.permutation profile xs of
 Just out->((bit profile,value xs),value out)
 _->error "invalid reference Poseidon2 fixture"
env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
entries :: [Entry]
entries=[Entry "crypto-poseidon2-koalabear16" "Full Poseidon2 KoalaBear16 permutation, published KAT and exact Bitcoin-verifier constants"
 "Poseidon2 eprint2023/323; Plonky3v0.5.1 KoalaBear16 default; Zirenf10a9b4b...poseidon2_init selected by pinned GOATNetwork/bitvm-gc"
 Eprint(Upstream "Plonky3 test_default_koalabear_poseidon2_width_16 full16-field KAT; other boundary/Ziren outputs derived by independent Integer dense-matrix reference")
 ["component only, not a complete SNARK/STARK verifier or byte-hash wrapper; one counting family for both parameter profiles",
  "KoalaBear q=2^31-2^24+1, width16, x^3 Sbox,8full+20partial rounds, initial diffusion; canonical32-bit operands",
  "False profile is published Plonky3 default KAT; True uses exact Ziren constants from the actual pinned Bitcoin-verifier dependency; those exact constants have no published outputKAT in the inspected source",
  "source code/constants are inert data; no downloaded Rust/Sage executed; complete field/permutation relation binds one aggregate witness"]
 (boundProgram kernel)
 ([Vector(if i==0 then "published default KoalaBear16 KAT" else "derived profile/boundary"++show i)env(encode x)Accept|(i,x)<-zip[0::Int ..]R.cases]++
  [Vector "noncanonical input x+q, normalized reference output" env ((Left(),value((R.q+head R.katInput):tail R.katInput)),value R.katExpected)Reject,
   Vector "wrong constant profile for otherwise valid KAT" env ((Right(),value R.katInput),value R.katExpected)Reject,
   Vector "same-CMR output corruption" env ((Left(),value R.katInput),value((head R.katExpected+1):tail R.katExpected))Reject])]
