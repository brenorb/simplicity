{-# LANGUAGE GADTs #-}
-- Same-CMR encoding regression probes preserved with the actual verifier.
module Main where
import Control.Exception (evaluate)
import System.IO (hFlush,stdout)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Digest (hash0)
import JetDiscovery.Tx
import JetDiscovery.Run (progCmr)
import JetDiscovery.Types
import qualified JetDiscovery.Corpus.Eprint as E

env=maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)
accepted (Prog p)=J.fastEval (J.unwrap (J.jetSubst p)) env ()==Just ()
main=mapM_ probe E.encodingProbes
 where
  probe (name,good,bad)=do
   let same=progCmr good==progCmr bad
   ok<-evaluate (accepted good)
   malformed<-evaluate (accepted bad)
   print (name,same,ok,malformed);hFlush stdout
   if same && ok && not malformed then pure () else error "canonical-encoding regression"
