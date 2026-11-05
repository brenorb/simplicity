{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 -funfolding-case-threshold=1 -funfolding-case-scaling=5 #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless,forM_)
import Data.List(isInfixOf)
import System.Environment(getArgs)
import System.Directory(doesFileExist)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import System.Mem(performGC)
import qualified JetDiscovery.Corpus.MlDsaNtt as Current
import qualified JetDiscovery.Diagnostics.NttFrozen as Frozen
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx(hashToInteger)
type Metrics=(Integer,Integer,Int,Int)
-- Force only the requested actual in-tree fields; what-if/ablations/mining are
-- separate final-run work. Both sides use the same first complete256polynomial.
metrics :: String -> Entry -> IO Metrics
metrics label(Entry ident _ _ _ _ _ program vectors)=do
 let measurement=measure(program(vecWitness(head vectors)))
     tuple=(mCmr measurement,mCost measurement,mProgBits measurement,mWitBits measurement)
 _<-evaluate(length(show tuple))
 print(label,ident,tuple)
 let(cmr,cost,bits,witnessBits)=tuple
 pure(hashToInteger cmr,cost,bits,witnessBits)
baselinePath="reports/data/ntt-baseline-metrics.txt"
validate old=do
 new<-metrics "current local transforms and small butterfly caches"(head Current.entries)
 print("canonical jetted CMR/cost/programbits/witnessbits unchanged",old==new)
 unless(old==new)(error "cache refactor changes canonical metric")
 performGC
 forM_ Current.entries$ \(Entry ident _ _ _ _ _ program vectors)->do
  putStrLn ident
  let cmr=progCmr(program(vecWitness(head vectors)))
  forM_(runVectors program cmr vectors)$ \r->do
   print(vrName r,vrOk r,vrNote r)
   unless(vrOk r&&not("prepared"`isInfixOf`vrNote r))(error "current full vector/path failed")
main=do
 hSetBuffering stdout LineBuffering
 args<-getArgs
 case args of
  ["baseline"]->do
   old<-metrics "frozen passed representation"(head Frozen.entries)
   exists<-doesFileExist baselinePath
   if exists then do prior<-read <$>readFile baselinePath;unless(prior==old)(error "immutable baseline differs")
    else writeFile baselinePath(show old++"\n")
  ["current"]->do old<-read <$>readFile baselinePath;validate old
  ["both"]->do old<-metrics "frozen passed representation"(head Frozen.entries);performGC;validate old
  _->error "usage: NttCacheEquivalence baseline|current|both"
