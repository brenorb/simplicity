module Main where
import Control.Monad (unless,forM)
import Control.Exception (evaluate)
import Data.Time.Clock
import GHC.Stats
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import System.Mem (performGC)
import JetDiscovery.Run
import JetDiscovery.Types
import qualified JetDiscovery.Corpus.NativePmmPool as D
import qualified JetDiscovery.Corpus.NativeLmsrMarket as L
import qualified JetDiscovery.Corpus.NativePendleMarket as P
import qualified JetDiscovery.Lib.ClaimLedger as C

main=do
 args<-getArgs
 case args of
  ["cmr",ident]->run ident Nothing
  ["vectors",ident,expected]->run ident (Just expected)
  _->error "usage: CheckPriorityMarketApps cmr ID | vectors ID EXPECTED_0x_CMR"
 where
  run wanted expected=case [e|e@(Entry ident _ _ _ _ _ _ _)<-D.entries++L.entries++P.entries,ident==wanted] of
   [Entry ident _ _ _ _ _ program vectors]->do
    begin<-getCurrentTime
    let first=case vectors of x:_->x;_->error "empty priority application"
        prog=program (vecWitness first)
        cmr=case expected of
         Just _->progCmr prog
         Nothing->case ident of
          "app-proactive-market-maker-private-pool"->C.cmrOf D.pmmT
          "app-lmsr-prediction-market"->C.cmrOf L.lmsrT
          "app-pendle-term-market-transition"->C.cmrOf P.termT
          _->error "missing typed dummy CMR case"
    say ("START canonical "++ident)
    evaluate (length (show cmr))
    say ("CMR "++ident++" "++show cmr)
    performGC
    stats<-getRTSStats
    end<-getCurrentTime
    say ("END canonical "++ident++" elapsed="++show (diffUTCTime end begin)++" max_live_bytes="++show (max_live_bytes stats)++" allocated_bytes="++show (allocated_bytes stats))
    case expected of
     Nothing->pure ()
     Just fixture->do
      unless (show cmr==fixture) (error "independent fixture CMR mismatch")
      say (ident++": fixture parity=True; preparing bound vector execution")
      oks<-forM (runVectors program cmr vectors) $ \r->do
       say (ident++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)
       pure (vrOk r)
      say ("TOTAL: 1 groups, "++show (length oks)++" vectors, "++(if and oks then "0" else "1")++" failed groups")
      unless (and oks) exitFailure
   _->error "unknown priority application ID"
  say s=putStrLn s>>hFlush stdout
