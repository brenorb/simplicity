{-# LANGUAGE RankNTypes,GADTs #-}
module Main where
import Control.Monad(forM_,unless)
import qualified Data.ByteString as B
import Data.List(isInfixOf)
import System.Environment(getArgs)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
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
  ["full"]->forM_ entries$ \(Entry ident _ _ _ _ _ program vectors)->do
   putStrLn ident
   let cmr=progCmr(program(vecWitness(head vectors)))
   print("canonical CMR unchanged",cmr==progCmr(Prog(unProg(program(vecWitness(head vectors))))))
   case boundView(program(vecWitness(head vectors)))of
    Just(BoundView kernel _)->do print("boundEligible",boundEligible kernel);unless(boundEligible kernel)(error "internal witness/disconnect")
    _->error "missing bound kernel"
   forM_(runVectors program cmr vectors)$ \r->do
    print(vrName r,vrOk r,vrNote r)
    unless(vrOk r&&"prepared"`isInfixOf`vrNote r)(error "full vector failed")
  _->error "usage: FairSwapProbe reference|helpers|full"
