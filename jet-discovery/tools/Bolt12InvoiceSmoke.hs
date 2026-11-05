{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import JetDiscovery.Lib.Bolt12Invoice(entry)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
check(Entry ident _ _ _ _ _ make vectors)=do
 let first=case vectors of v:_->make(vecWitness v);_->error "empty suite"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView k _)->boundEligible k;_->False
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 _<-evaluate eligible
 putStrLn("prepared_kernel_eligible="++show eligible++" CMR="++show cmr);hFlush stdout
 results<-mapM(\r->do
   _<-evaluate(vrOk r)
   putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show(vrOk r));hFlush stdout
   return(vrOk r))(runVectors make cmr vectors)
 unless(eligible&&and results)exitFailure
 putStrLn "all BOLT12 invoice cases pass with per-vector canonical CMR checks"
main=entry>>=check
