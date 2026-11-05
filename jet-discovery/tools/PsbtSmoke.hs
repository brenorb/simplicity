{-# LANGUAGE RankNTypes #-}
-- Execute every actual canonical PSBT client vector under one CMR.
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import JetDiscovery.Lib.Psbt(entry)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import System.Exit(exitFailure)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
main=do
 hSetBuffering stdout LineBuffering
 entry>>=check
check(Entry ident _ _ _ _ _ make vectors)=do
 let first=case vectors of v:_->make(vecWitness v);_->error "empty"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
 _<-evaluate eligible
 putStrLn(ident++" vectors="++show(length vectors)++" prepared_kernel_eligible="++show eligible++" CMR="++show cmr)
 results<-forM(runVectors make cmr vectors)$ \r->do
  ok<-evaluate(vrOk r)
  putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show ok)
  return ok
 unless(eligible&&length vectors==23&&and results)exitFailure
 putStrLn "all published/fresh PSBT finalizer/extractor vectors pass with per-vector canonical CMR"
