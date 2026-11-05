module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
import JetDiscovery.Corpus.TransportCrypto
import JetDiscovery.Types
import JetDiscovery.Run
check(Entry ident _ _ _ _ _ program vectors)=do
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 let cmr=progCmr(program(vecWitness(head vectors)))
 putStrLn("canonical CMR="++show cmr);hFlush stdout
 outcomes<-mapM(\v->do
   ok<-evaluate(vrOk v)
   putStrLn(vrName v++": "++show ok++" "++vrNote v);hFlush stdout
   pure ok)(runVectors program cmr vectors)
 unless(and outcomes)exitFailure
main=entries>>=mapM_ check
