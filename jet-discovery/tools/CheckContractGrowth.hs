module Main where
import Control.Monad (forM,unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import JetDiscovery.Types
import JetDiscovery.Run
import qualified JetDiscovery.Corpus.ContractGrowth as G
main :: IO ()
main=do
 args<-getArgs
 let selected=[e|e@(Entry ident _ _ _ _ _ _ _)<-G.entries,null args||ident `elem` args]
 groups<-forM selected $ \(Entry ident _ _ _ _ _ program vectors)->do
  let cmr=case vectors of v:_->progCmr (program (vecWitness v));_->error "empty vector set"
  let batch=runVectors program cmr vectors
  results<-forM batch $ \r->do
   putStrLn (ident++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)
   hFlush stdout
   pure r
  putStrLn (ident++": "++show (length results)++" vectors; "++if all vrOk results then "PASS" else "FAIL")
  hFlush stdout
  pure (length results,all vrOk results)
 putStrLn ("TOTAL: "++show (length groups)++" groups, "++show (sum (map fst groups))++" vectors, "++show (length (filter (not . snd) groups))++" failed groups")
 unless (all snd groups) exitFailure
