{-# LANGUAGE RankNTypes,GADTs #-}
module Main where
import Control.Monad(forM_,unless)
import Control.Exception(evaluate)
import qualified Data.ByteString as B
import Data.List(isInfixOf)
import System.Environment(getArgs)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import System.Mem(performGC)
import GHC.Clock(getMonotonicTimeNSec)
import GHC.Stats(getRTSStats,gc,gcdetails_live_bytes)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Corpus.FairSwap
import qualified JetDiscovery.Ref.FairSwap as R
import qualified JetDiscovery.Ref.Bip340 as Bip
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import JetDiscovery.Run
main=do
 hSetBuffering stdout LineBuffering
 args<-getArgs
 case args of
  ["reference"]->do print("formal fixed-wiring complaint reference",referenceAudit);unless referenceAudit(error "reference audit failed")
  ["helpers"]->do
   let key=Bip.bytesFromInt 991;chunks=[Bip.bytesFromInt i|i<-[10..13]];cs=R.cipherNodes key chunks
       Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
       pack(c,[a,b,d])=(w256FromBytes c,(w256FromBytes a,(w256FromBytes b,w256FromBytes d)))
       pack _=error "proof dimension"
       hdr=R.header key chunks;(a,(b,c))=hdr;header=(w256FromBytes a,(w256FromBytes b,w256FromBytes c))
   forM_[0..6]$ \i->do
    let got=J.fastEval(J.unwrap(J.jetSubst(openingRoot i)))env(pack(R.opening cs i))
        ok=got==Just(w256FromBytes(R.cipherTree cs))
    print("ciphertext opening",i,ok);unless ok(error "Merkle helper failed")
   forM_[(0,B.replicate 32 0),(1,key),(1,Bip.bytesFromInt 992)]$ \(phase,k)->do
    let got=J.fastEval(J.unwrap(J.jetSubst(stateT phase)))env(header,w256FromBytes k)
        ok=got==Just(w256FromBytes(R.stateBytes(fromInteger phase)hdr k))
    print("state commitment",phase,ok);unless ok(error "state hash failed")
  ["full"]->do
   -- Native signature fixture generation needs the canonical program root.
   -- Force its small retained value before constructing the signed program,
   -- avoiding nested whole-program construction hidden inside witness data.
   putStrLn "canonical unsigned seed construction: started"
   started<-getMonotonicTimeNSec
   _<-evaluate(hashToInteger saleCmr)
   performGC
   stats<-getRTSStats
   finished<-getMonotonicTimeNSec
   print("canonical unsigned seed construction: completed",saleCmr,
    "elapsed seconds",fromIntegral(finished-started)/1e9::Double,
    "live bytes after GC",gcdetails_live_bytes(gc stats))
   full
  _->error "usage: FairSwapProbe reference|helpers|full"
full=forM_ entries$ \(Entry ident _ _ _ _ _ program vectors)->do
   putStrLn ident
   putStrLn "canonical signed fixture construction: started"
   let cmr=progCmr(program(vecWitness(head vectors)))
   let sameCmr=cmr==progCmr(Prog(unProg(program(vecWitness(head vectors)))))
   print("canonical CMR unchanged",sameCmr);unless sameCmr(error "prepared composition CMR changed")
   unless(cmr==saleCmr)(error "signed fixture changed canonical seed CMR")
   putStrLn "canonical signed fixture construction: completed"
   prepared<-case boundView(program(vecWitness(head vectors)))of
    Just(BoundView kernel _)->do print("boundEligible",boundEligible kernel);unless(boundEligible kernel)(error "internal witness/disconnect");pure True
    _->do putStrLn "ordinary staged execution: shared header once, independent branch fields consumed once";pure False
   forM_(runVectors program cmr vectors)$ \r->do
    print(vrName r,vrOk r,vrNote r)
    unless(vrOk r&&("prepared"`isInfixOf`vrNote r)==prepared)(error "full vector/path failed")
