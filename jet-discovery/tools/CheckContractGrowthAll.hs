module Main where
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import JetDiscovery.Types
import JetDiscovery.Run
import qualified JetDiscovery.Corpus.ContractGrowth as G
import qualified JetDiscovery.Corpus.ContractMessageApps as M
import qualified JetDiscovery.Corpus.ContractBridge as V
main :: IO ()
main=do
 args<-getArgs
 let selected=[e|e@(Entry ident _ _ _ _ _ _ _)<-G.entries++M.entries++V.entries,null args||ident `elem` args]
 results<-forM selected $ \(Entry ident _ _ _ _ _ program vectors)->do
  let first=case vectors of v:_->v;_->error "empty growth group"
      p=program (vecWitness first)
      cmr=progCmr p
      eligible=case boundView p of Just (BoundView kernel _)->boundEligible kernel;_->False
      batch=runVectors program cmr vectors
  say (ident++": bound kernel eligible="++show eligible)
  checks<-forM batch $ \r->do
   say (ident++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)
   pure (vrOk r)
  say (ident++": "++show (length checks)++" current guarded vectors; "++if and checks then "PASS" else "FAIL")
  pure (length checks,and checks)
 say ("TOTAL: "++show (length results)++" groups, "++show (sum (map fst results))++" vectors, "++show (length (filter (not . snd) results))++" failed groups")
 unless (all snd results) exitFailure
 where say s=putStrLn s>>hFlush stdout
