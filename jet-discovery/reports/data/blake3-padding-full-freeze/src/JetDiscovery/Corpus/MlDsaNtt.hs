{-# LANGUAGE GADTs,ScopedTypeVariables,RankNTypes #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 -funfolding-case-threshold=1 -funfolding-case-scaling=5 #-}
-- | FIPS204 Algorithms41/42 complete degree256 NTT and inverse. Both directions
-- are one arithmetic component family; no ML-DSA signature verification credit.
-- GHC9.8.4 needs the compilation-only simplifier allowance for this large TyC
-- dictionary; it changes neither the Simplicity expression nor its jet costs.
module JetDiscovery.Corpus.MlDsaNtt(entries,forwardT,inverseT,Poly) where
import Prelude hiding(drop,take,not,and,or)
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Bitcoin.Term(Simplicity,Primitive)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import qualified Simplicity.Ty.Word as Ty
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.MlDsaNtt as R
type Poly=Vector256 Word32
k32 :: (Core t,TyC a) => Integer -> t a Word32
k32=konst.w32
canon :: Assert t => t Word32 Word32
canon=((iden&&&k32 R.q)>>>A.subtract word32)&&&iden>>>
 ((ooh&&&(ih&&&oih))>>>cond oh ih)
addRef,subRef,mulRef :: Assert t => t(Word32,Word32)Word32
addRef=A.add word32>>>ih>>>canon
subRef=A.subtract word32>>>cond(iden&&&k32 R.q>>>A.add word32>>>ih)iden
mulRef=(A.multiply word32&&&konst(w64 R.q))>>>A.div_mod word64>>>ih>>>ih
{-# NOINLINE addWrapped #-}
addWrapped :: J.WrappedSimplicity (Word32,Word32) Word32
addWrapped=J.jetSubst addRef
{-# NOINLINE subWrapped #-}
subWrapped :: J.WrappedSimplicity (Word32,Word32) Word32
subWrapped=J.jetSubst subRef
{-# NOINLINE mulWrapped #-}
mulWrapped :: J.WrappedSimplicity (Word32,Word32) Word32
mulWrapped=J.jetSubst mulRef
addF,subF,mulF :: Simplicity t => t(Word32,Word32)Word32
addF=J.unwrap addWrapped
subF=J.unwrap subWrapped
mulF=J.unwrap mulWrapped

-- Entire independent halves are transformed together. Each butterfly's product
-- enters its add/sub pair once rather than being recomputed for two outputs.
butterfly :: Simplicity t => Ty.Vector Word32 v -> Integer -> t(v,v)(v,v)
butterfly SingleV z=(oh&&&((ih&&&k32 z)>>>mulF))>>>(addF&&&subF)
butterfly(DoubleV v)z=(((ooh&&&ioh)>>>butterfly v z)&&&((oih&&&iih)>>>butterfly v z))>>>
 ((ooh&&&ioh)&&&(oih&&&iih))
inverseButterfly :: Simplicity t => Ty.Vector Word32 v -> Integer -> t(v,v)(v,v)
inverseButterfly SingleV z=addF&&&((subF&&&k32 z)>>>mulF)
inverseButterfly(DoubleV v)z=(((ooh&&&ioh)>>>inverseButterfly v z)&&&((oih&&&iih)>>>inverseButterfly v z))>>>
 ((ooh&&&ioh)&&&(oih&&&iih))
stage :: Simplicity t => Int -> Int -> Ty.Vector Word32 v -> t v v
stage 0 k(DoubleV v)=butterfly v(R.zetas!!k)
stage d k(DoubleV v)=take(stage(d-1)(2*k)v)&&&drop(stage(d-1)(2*k+1)v)
stage _ _ SingleV=error "MLDSA stage exceeds polynomial size"
invStage :: Simplicity t => Int -> Int -> Ty.Vector Word32 v -> t v v
invStage 0 k(DoubleV v)=inverseButterfly v(negate(R.zetas!!k)`mod`R.q)
invStage d k(DoubleV v)=take(invStage(d-1)k v)&&&drop(invStage(d-1)(k-2^(d-1))v)
invStage _ _ SingleV=error "MLDSA inverse stage exceeds polynomial size"
mapPoly :: Core t => Ty.Vector Word32 v -> t Word32 Word32 -> t v v
mapPoly SingleV f=f
mapPoly(DoubleV v)f=take(mapPoly v f)&&&drop(mapPoly v f)
forwardRef :: Simplicity t => t Poly Poly
forwardRef=L.foldl'(>>>)iden[stage d 1 vector256|d<-[0..7]]
inverseRef :: Simplicity t => t Poly Poly
inverseRef=L.foldl'(>>>)iden[invStage d(2^(d+1)-1)vector256|d<-[7,6..0]]>>>
 mapPoly vector256((iden&&&k32 8347681)>>>mulF)
{-# NOINLINE forwardWrapped #-}
forwardWrapped :: J.WrappedSimplicity Poly Poly
forwardWrapped=J.jetSubst forwardRef
{-# NOINLINE inverseWrapped #-}
inverseWrapped :: J.WrappedSimplicity Poly Poly
inverseWrapped=J.jetSubst inverseRef
forwardT,inverseT :: Simplicity t => t Poly Poly
forwardT=J.unwrap forwardWrapped
inverseT=J.unwrap inverseWrapped
canonical :: Assert t => Ty.Vector Word32 v -> t v ()
canonical SingleV=(iden&&&k32 R.q)>>>A.lt word32>>>verify
canonical(DoubleV v)=(take(canonical v)&&&drop(canonical v))>>>unit
type Input=((Bit,Poly),Poly)
kernel :: Simplicity t => t Input ()
kernel=((oh>>>ih>>>canonical vector256)&&&(((oh>>>cond inverseT forwardT)&&&ih)>>>eq>>>verify))>>>unit
-- Expected coefficients are independent final comparisons. They are not carried
-- beside the complete polynomial through all8transform stages. Each coefficient
-- witness occurs once, and recursive projections discard the compared halves.
-- Shared direction/input enter together exactly once. This ordinary Prog does
-- not pretend to be an eligible witness-free prepared kernel.
program :: Input -> Prog
program (input,expected)=Prog(witness input>>>(checked&&&iden)>>>ih>>>
 cond inverseT forwardT>>>checkExpected vector256 expected)
 where
  checked :: forall t. Simplicity t => t(Bit,Poly)()
  checked=ih>>>canonical vector256
  checkExpected :: forall t v. Simplicity t => Ty.Vector Word32 v -> v -> t v ()
  checkExpected SingleV x=(iden&&&witness x)>>>eq>>>verify
  checkExpected(DoubleV v)(a,b)=(take(checkExpected v a)&&&drop(checkExpected v b))>>>unit
value :: [Integer] -> Poly
value xs | length xs/=256=error "MLDSA polynomial requires exactly256coefficients"
         | otherwise=case fst(bufferFill buffer511(map w32 xs))of (Right a,_)->a;_->error "MLDSA vector fill"
bit x=if x then Right()else Left()
encode inverse xs=case(if inverse then R.inverse xs else R.forward xs)of
 Just ys->((bit inverse,value xs),value ys)
 Nothing->error "invalid MLDSA reference fixture"
env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
entries :: [Entry]
entries=[Entry "crypto-ml-dsa-ntt256" "Full FIPS204 degree256 NTT and inverse over q8380417"
 "FIPS204 sections2.5/7.5, equation2.1 and Algorithms41-43; vendor-specs/crypto-growth/fips204.pdf"
 PostQuantum(Derived "complete independent direct-DFT/inverse polynomial evaluation and FIPS butterfly cross-checks; six full polynomials each direction; no separate official NTT outputKAT found in the standard")
 ["arithmetic component only; no signature decoding, SHAKE expansion, challenge/hint/norm checks and no full ML-DSA verifier credit",
  "all256coefficients and all8stages, canonical residues0..q-1; zeta1753, bit-reversed twiddle order and exact inverse scale8347681",
  "both directions and all ML-DSA parameter profiles share ONE counting family; direction and input bound once, each expected coefficient bound once at its final comparison",
  "published-equation derived vectors are explicitly distinguished from official signatureKATs, which this isolated transform does not verify"]
 program
 ([Vector((if inverse then "inverse" else "forward")++" full polynomial"++show i)env(encode inverse xs)Accept|inverse<-[False,True],(i,xs)<-zip[0::Int ..]R.cases]++
  [Vector "noncanonical input q" env ((Left(),value(R.q:replicate 255 0)),value(replicate 256 0))Reject,
   Vector "same-CMR output corruption" env ((Left(),value(1:replicate 255 0)),value(2:replicate 255 1))Reject,
   Vector "wrong transform direction" env ((Right(),value(1:replicate 255 0)),value(replicate 256 1))Reject])]
