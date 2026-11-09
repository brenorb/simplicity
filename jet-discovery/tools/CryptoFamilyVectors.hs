{-# LANGUAGE GADTs,RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM_,unless)
import Data.List(isInfixOf)
import qualified Data.ByteString as BS
import System.Environment(getArgs)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Corpus.Blake3 as B3
import qualified JetDiscovery.Corpus.Shake256 as Xof
import qualified JetDiscovery.Corpus.MlDsaNtt as Ntt
import qualified JetDiscovery.Corpus.Poseidon2 as P2
import qualified JetDiscovery.Ref.Blake3 as RB3
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import JetDiscovery.Run

compressionExpr :: J.WrappedSimplicity (Vector8 Word32,(Vector16 Word32,(Word64,(Word32,Word32))))(Vector16 Word32)
compressionExpr=J.jetSubst B3.compressT
chainingExpr :: J.WrappedSimplicity (Vector8 Word32,(Vector16 Word32,(Word64,(Word32,Word32))))(Vector8 Word32)
chainingExpr=J.jetSubst B3.compressChainingT
v8 xs=case fst(bufferFill buffer15(map(w32.toInteger)xs))of(Right a,_)->a;_->error "v8"
v16 xs=case fst(bufferFill buffer31(map(w32.toInteger)xs))of(Right a,_)->a;_->error "v16"
compression=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
 forM_ [(replicate 16 0,0,0,11),([0..15],0,64,3),([0..15],1,64,2),([0..15],2^32+3,63,0)] $ \(m,counter,len,flags)->do
  let got=J.fastEval(J.unwrap compressionExpr)env(v8 RB3.iv,(v16 m,(w64 counter,(w32 len,w32 flags))))
      expected=v16(RB3.compress RB3.iv m(fromInteger counter)(fromInteger len)(fromInteger flags))
      ok=got==Just expected
  print("complete BLAKE3 compression",counter,len,flags,ok)
  unless ok(error "BLAKE3 compression mismatch")
chaining=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
     derivedCV=take 8(RB3.compress RB3.iv[0..15]0 64 1)
     cases=[(RB3.iv,replicate 16 0,0,0,11),(RB3.iv,[0..15],0,64,3),(RB3.iv,[0..15],1,64,2),(RB3.iv,[0..15],2^32+3,63,0),
       (replicate 8 0,[0..15],0,64,12),([1..8],replicate 16 maxBound,2^64-1,63,0),
       (derivedCV,[17..32],0,64,0),(derivedCV,[17..32],1,64,10)]
 forM_ cases$ \(cv,m,counter,len,flags)->do
  let got=J.fastEval(J.unwrap chainingExpr)env(v8 cv,(v16 m,(w64 counter,(w32 len,w32 flags))))
      expected=v8(take 8(RB3.compress cv m(fromInteger counter)(fromInteger len)(fromInteger flags)))
      ok=got==Just expected
  print("BLAKE3 exact first8compression words",counter,len,flags,ok)
  unless ok(error "BLAKE3 chaining compression mismatch")
paddingExpr :: J.WrappedSimplicity(Word8,Word512)()
paddingExpr=J.jetSubst B3.canonicalBlockT
padding=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
     raw bytes=toWord word512(BS.foldl'(\a b->256*a+toInteger b)0 bytes)
     prefix n=BS.pack[fromIntegral(1+i`mod`250)|i<-[0..n-1]]
     cases=[("valid prefix",n,prefix n<>BS.replicate(64-n)0,True)|n<-[0..64]]++
      [("first unused byte nonzero",n,prefix n<>BS.singleton 1<>BS.replicate(63-n)0,False)|n<-[0..63]]++
      [("out of range",65,BS.replicate 64 0,False)]
 forM_ cases$ \(name,n,bytes,expected)->do
  let accepted=J.fastEval(J.unwrap paddingExpr)env(w8(toInteger n),raw bytes)==Just()
      ok=accepted==expected
  print(name,n,ok);unless ok(error "BLAKE3 canonical block mismatch")
main=do
 hSetBuffering stdout LineBuffering
 args<-getArgs
 case args of
  ["blake3-compression"]->compression
  ["blake3-padding"]->padding
  ["blake3-chaining"]->chaining
  _->do
   entries<-case args of
    ["blake3"]->B3.entries
    ["shake"]->Xof.entries
    ["ntt"]->pure Ntt.entries
    ["poseidon2"]->pure P2.entries
    _->error "usage: CryptoFamilyVectors blake3-compression|blake3|shake|ntt|poseidon2"
   forM_ entries $ \(Entry i _ _ _ _ _ program vectors)->do
    putStrLn i
    case vectors of
     []->error "no vectors"
     first:_->do
      let p=program(vecWitness first);cmr=progCmr p
      print("canonical composition CMR unchanged",cmr==progCmr(Prog(unProg p)))
      unless(cmr==progCmr(Prog(unProg p)))(error "prepared composition CMR changed")
      prepared<-case boundView p of
       Just(BoundView k _)->do print("boundEligible",boundEligible k);unless(boundEligible k)(error "kernel contains witness/disconnect");pure True
       _->do putStrLn "ordinary execution: independently consumed internal witnesses, no prepared kernel";pure False
      forM_(runVectors program cmr vectors)$ \r->do
       ok<-evaluate(vrOk r);print(vrName r,ok,vrNote r)
       unless(("prepared"`isInfixOf`vrNote r)==prepared)(error "execution path observability mismatch")
       unless ok(error "vector or same-CMR failure")
