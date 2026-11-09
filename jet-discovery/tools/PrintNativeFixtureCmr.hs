module Main where
import Control.Monad (forM_)
import Control.Exception (evaluate)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import System.Mem (performGC)
import Data.Time.Clock
import GHC.Stats
import JetDiscovery.Types
import JetDiscovery.Run
import qualified JetDiscovery.Corpus.NativeLoan as L
import qualified JetDiscovery.Corpus.NativeBatchOrders as B
import qualified JetDiscovery.Corpus.NativeOcr as O
import qualified JetDiscovery.Corpus.StablePool as S
import qualified JetDiscovery.Corpus.WeightedPool as W
main=do
 args<-getArgs
 forM_ [e|e@(Entry ident _ _ _ _ _ _ _)<-L.entries++B.entries++O.entries++S.entries++W.entries,ident `elem`args] $ \(Entry ident _ _ _ _ _ program vectors)->do
  begin<-getCurrentTime
  say ("START canonical "++ident)
  let cmr=progCmr (program (vecWitness (head vectors)))
  evaluate (length (show cmr))
  say ("CMR "++ident++" "++show cmr)
  performGC
  stats<-getRTSStats
  end<-getCurrentTime
  say ("END canonical "++ident++" elapsed="++show (diffUTCTime end begin)++" max_live_bytes="++show (max_live_bytes stats)++" allocated_bytes="++show (allocated_bytes stats))
 where say s=putStrLn s>>hFlush stdout
