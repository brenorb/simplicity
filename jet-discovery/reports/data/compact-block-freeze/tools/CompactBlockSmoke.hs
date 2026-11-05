{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Lib.CompactBlock(entry)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import JetDiscovery.Tx(hashFromInteger)
import System.Exit(exitFailure)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
main=do hSetBuffering stdout LineBuffering;entry>>=check
check(Entry ident _ _ _ _ _ make vectors)=do
 functional<-forM vectors$ \v->do
  let ok=case vecEnv v(hashFromInteger 1)of
        Just env->(J.fastEval(unProg(make(vecWitness v)))env()==Just())==(vecExpect v==Accept)
        _->False
  _<-evaluate ok;putStrLn("actual functional "++vecName v++" pass="++show ok);return ok
 unless(and functional)exitFailure
 let first=case vectors of v:_->make(vecWitness v);_->error "empty"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
 _<-evaluate eligible
 putStrLn(ident++" vectors="++show(length vectors)++" prepared_kernel_eligible="++show eligible++" CMR="++show cmr)
 results<-forM(runVectors make cmr vectors)$ \r->do
  ok<-evaluate(vrOk r);putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show ok);return ok
 unless(eligible&&and results)exitFailure
 putStrLn "all complete compact-block client vectors pass with per-vector canonical CMR"
