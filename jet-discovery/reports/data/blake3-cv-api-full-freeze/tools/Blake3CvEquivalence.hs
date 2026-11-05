{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM_,unless)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import System.Mem(performGC)
import qualified Simplicity.Bitcoin.Dag as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Serialization.BitString as Bits
import Simplicity.MerkleRoot(CommitmentRoot,commitmentRoot)
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Cost(TermWeight,milliWeigh)
import qualified JetDiscovery.Corpus.Blake3 as B3
import qualified JetDiscovery.Diagnostics.Blake3CvFrozen as Frozen
import qualified JetDiscovery.Ref.Blake3 as R
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
type Input=(Vector8 Word32,(Vector16 Word32,(Word64,(Word32,Word32))))
type Output=Vector8 Word32
{-# NOINLINE original #-}
original :: J.WrappedSimplicity Input Output
original=J.jetSubst Frozen.compressChainingT
{-# NOINLINE current #-}
current :: J.WrappedSimplicity Input Output
current=J.jetSubst B3.compressChainingT
{-# NOINLINE pureSpec #-}
pureSpec :: J.WrappedSimplicity Input Output
pureSpec=J.jetSubst B3.compressChainingSpec
metrics label wrapped=do
 let cmr=commitmentRoot(J.unwrap wrapped::CommitmentRoot Input Output)
     cost=milliWeigh(J.unwrap wrapped::TermWeight Input Output)
     dag=D.jetDag(J.unwrap wrapped::D.JetDag J.JetType Input Output)
     code=length(Bits.putDagNoWitnessLengthCode dag)
     witness=case Bits.putWitnessData dag of Just b->length b;_->error "kernel witness serialization"
     tuple=(cmr,cost,code,witness)
 _<-evaluate(length(show tuple))
 print(label,tuple)
 pure tuple
v8 xs=case fst(bufferFill buffer15(map(w32.toInteger)xs))of(Right a,_)->a;_->error "v8"
v16 xs=case fst(bufferFill buffer31(map(w32.toInteger)xs))of(Right a,_)->a;_->error "v16"
controls label wrapped=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
     chained=take 8(R.compress R.iv[0..15]0 64 1)
     cases=[(R.iv,replicate 16 0,0,0,11),(R.iv,[0..15],0,64,3),(R.iv,[0..15],1,64,2),(R.iv,[0..15],2^32+3,63,0),
       (replicate 8 0,[0..15],0,64,12),([1..8],replicate 16 maxBound,2^64-1,63,0),
       (chained,[17..32],0,64,0),(chained,[17..32],1,64,10)]
 forM_(zip[0::Int ..]cases)$ \(i,(cv,m,counter,len,flags))->do
  let expected=v8(take 8(R.compress cv m(fromInteger counter)(fromInteger len)(fromInteger flags)))
      answer=J.fastEval(J.unwrap wrapped)env(v8 cv,(v16 m,(w64 counter,(w32 len,w32 flags))))
      ok=answer==Just expected
  print(label,i,ok);unless ok(error "independent CV compression control failed")
main=do
 hSetBuffering stdout LineBuffering
 before<-metrics "frozen before pure API" original
 performGC
 after<-metrics "current native application helper" current
 print("native jetted CMR/cost/reference-codebits/witnessbits unchanged",before==after)
 unless(before==after)(error "native application expression changed")
 performGC
 spec<-metrics "Assert-only pure candidate specification" pureSpec
 print("pure spec exactly matches actual native helper",before==spec)
 unless(before==spec)(error "pure candidate specification differs")
 controls "frozen independent CV" original
 controls "current independent CV" current
 controls "pure independent CV" pureSpec
