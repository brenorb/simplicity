{-# LANGUAGE GADTs #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM_,unless)
import Data.List(isInfixOf)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import JetDiscovery.Corpus.Poseidon2
import qualified JetDiscovery.Ref.Poseidon2 as R
import JetDiscovery.Types
import JetDiscovery.Run
main=do
 hSetBuffering stdout LineBuffering
 print("published reference KAT",R.selfCheck)
 unless R.selfCheck(error "Poseidon2 reference KAT failed")
 forM_ entries $ \(Entry i _ _ _ _ _ program vectors)->do
  putStrLn i
  case vectors of
   []->error "no vectors"
   first:_->do
    let p=program(vecWitness first);cmr=progCmr p
    print("canonical CMR unchanged",cmr==progCmr(Prog(unProg p)))
    unless(cmr==progCmr(Prog(unProg p)))(error "prepared composition CMR changed")
    case boundView p of Just(BoundView k _)->unless(boundEligible k)(error "kernel has internal witness/disconnect");_->error "missing bound kernel"
    forM_ (runVectors program cmr vectors) $ \r->do
     ok<-evaluate(vrOk r);print(vrName r,ok,vrNote r)
     unless("prepared"`isInfixOf`vrNote r)(error "prepared path not observed")
     unless ok(error "Poseidon2 vector or CMR failure")
