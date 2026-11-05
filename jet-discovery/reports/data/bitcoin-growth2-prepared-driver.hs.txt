{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Corpus.BitcoinGrowth2(entries)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import System.Environment(getArgs)
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
check(Entry ident _ _ _ _ _ make vectors)=do
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 let first=case vectors of v:_->make(vecWitness v);_->error "empty vector suite"
     baseline=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
     expectedRoot=lookup ident[("app-silent-payment-output-covenant","0x7ac619277ae12417468d7f39e1b51f7a085a2a9a3e79d43deb35377997fc3608"),("app-reserve-ownership-and-sum","0xdcdf2a0b66e03c9c12db442bb6684bd5226692cf39469dd18e884c9ed7f9cd8c")]
     sameHistorical=maybe True(==show baseline)expectedRoot
 _<-evaluate(sameHistorical&&eligible)
 putStrLn("  prepared_kernel_eligible="++show eligible++" historical_cmr_unchanged="++show sameHistorical);hFlush stdout
 results<-mapM(\result->do
  _<-evaluate(vrOk result)
  putStrLn("  "++vrName result++" expected="++show(vrExpect result)++" actual="++vrNote result++" pass="++show(vrOk result));hFlush stdout
  return(vrOk result))(runVectors make baseline vectors)
 putStrLn("  CMR="++show baseline);hFlush stdout
 return(sameHistorical&&eligible&&and results)
main=do
 programs<-entries;filters<-getArgs
 let selected=if null filters then programs else filter(\e->entryId e `elem` filters)programs
 unless(not(null selected))exitFailure
 outcomes<-mapM check selected
 unless(and outcomes)exitFailure
 putStrLn "all BitcoinGrowth2 vectors pass with stable CMR"
