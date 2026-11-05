{-# LANGUAGE RankNTypes #-}
-- Standalone low-memory same-CMR vector validation; imports the new module only.
module Main where
import Control.Exception (evaluate)
import Control.Monad (unless)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Corpus.BitcoinGrowth (entries)
import JetDiscovery.Types
import JetDiscovery.Run (progCmr)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)

check (Entry ident _ _ _ _ _ make vectors)=do
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 let baseline=progCmr(make(vecWitness(head vectors)))
 results<-mapM (\(Vector name env w expected)->do
   let p=make w
       same=progCmr p==baseline
       accepted=case p of
         Prog term->case env baseline of
           Nothing->False
           Just pe->J.fastEval(J.unwrap(J.jetSubst term))pe()==Just()
       ok=same&&accepted==(expected==Accept)
   _<-evaluate ok
   putStrLn("  "++name++" same_cmr="++show same++" accepts="++show accepted++" expected="++show expected++" pass="++show ok)
   hFlush stdout
   return ok) vectors
 putStrLn("  CMR="++show baseline)
 return(and results)
main=do
 programs<-entries
 filters<-getArgs
 let selected=if null filters then programs else filter(\e->entryId e `elem` filters)programs
 unless(not(null selected))exitFailure
 results<-mapM check selected
 unless(and results)exitFailure
 putStrLn "all BitcoinGrowth vectors pass with stable CMR"
