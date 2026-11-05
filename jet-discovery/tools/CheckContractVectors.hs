{-# LANGUAGE ExistentialQuantification #-}
module Main where
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import JetDiscovery.Types
import JetDiscovery.Run (progCmr,runVectors,vrOk,vrName,vrNote)
import qualified JetDiscovery.Corpus.BitcoinExpansion as B
import qualified JetDiscovery.Corpus.ContractExpansion as C
import qualified JetDiscovery.Corpus.ContractMath as M
import qualified JetDiscovery.Corpus.FinancialApps as F
import qualified JetDiscovery.Corpus.StatefulApps as S
import qualified JetDiscovery.Corpus.ProposalApps as P
import qualified JetDiscovery.Corpus.StateMachines as T
main :: IO ()
main=do
 args<-getArgs
 let allEntries=B.entries++C.entries++M.entries++F.entries++S.entries++P.entries++T.entries
     selected=case args of ["remaining"]->drop (length B.entries) allEntries;["contract"]->C.entries;_->allEntries
 outcomes<-forM selected $ \(Entry ident _ _ _ _ _ program vectors)->do
  let results=case vectors of []->error "empty vectors";(v:_)->runVectors program (progCmr (program (vecWitness v))) vectors
      bad=filter (not . vrOk) results
  putStrLn (ident++": "++show (length results)++" vectors; "++if null bad then "PASS" else "FAIL")
  mapM_ (\v->putStrLn ("  "++vrName v++": "++vrNote v)) bad
  hFlush stdout
  pure (null bad,length results)
 putStrLn ("TOTAL: "++show (length outcomes)++" groups, "++show (sum (map snd outcomes))++" vectors, "++show (length (filter (not . fst) outcomes))++" failed groups")
 unless (all fst outcomes) exitFailure
