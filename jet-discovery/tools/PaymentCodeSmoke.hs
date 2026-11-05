{-# LANGUAGE RankNTypes #-}
-- Actual canonical bound-program execution; no reference-only count credit.
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import JetDiscovery.Lib.PaymentCode(entry)
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
 unless(eligible&&length vectors==19&&and results)exitFailure
 putStrLn "all BIP47 private-client vectors pass with per-vector canonical CMR"
