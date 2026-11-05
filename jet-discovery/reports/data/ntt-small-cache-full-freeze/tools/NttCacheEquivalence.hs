{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 -funfolding-case-threshold=1 -funfolding-case-scaling=5 #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless,forM_)
import Data.List(isInfixOf)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import System.Mem(performGC)
import qualified JetDiscovery.Corpus.MlDsaNtt as Current
import qualified JetDiscovery.Diagnostics.NttFrozen as Frozen
import JetDiscovery.Types
import JetDiscovery.Run
-- Force only the requested actual in-tree fields; what-if/ablations/mining are
-- separate final-run work. Both sides use the same first complete256polynomial.
metrics label(Entry ident _ _ _ _ _ program vectors)=do
 let measurement=measure(program(vecWitness(head vectors)))
     tuple=(mCmr measurement,mCost measurement,mProgBits measurement,mWitBits measurement)
 _<-evaluate(length(show tuple))
 print(label,ident,tuple)
 pure tuple
main=do
 hSetBuffering stdout LineBuffering
 old<-metrics "frozen passed representation"(head Frozen.entries)
 performGC
 new<-metrics "current small butterfly caches"(head Current.entries)
 print("canonical jetted CMR/cost/programbits/witnessbits unchanged",old==new)
 unless(old==new)(error "cache refactor changes canonical metric")
 performGC
 forM_ Current.entries$ \(Entry ident _ _ _ _ _ program vectors)->do
  putStrLn ident
  let cmr=progCmr(program(vecWitness(head vectors)))
  forM_(runVectors program cmr vectors)$ \r->do
   print(vrName r,vrOk r,vrNote r)
   unless(vrOk r&&not("prepared"`isInfixOf`vrNote r))(error "current full vector/path failed")
