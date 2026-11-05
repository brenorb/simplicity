{-# LANGUAGE RankNTypes #-}
-- Standalone same-CMR adversarial tests for the authenticated context compiler.
module Main where

import qualified JetDiscovery.Ref.FibonacciStark as F
import qualified JetDiscovery.Ref.StarkContext as C
import qualified JetDiscovery.Corpus.FibonacciStark as V
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.MerkleRoot (CommitmentRoot,commitmentRoot)
import JetDiscovery.Types
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import Control.Exception (evaluate)
import Control.Monad (unless)
import System.Exit (exitFailure)
import System.CPUTime (getCPUTime)
import System.IO (hFlush,stdout)
import GHC.Stats (getRTSStats,max_live_bytes,allocated_bytes)

phase label action=do
  putStrLn(label++" starting");hFlush stdout
  before<-getCPUTime
  answer<-action
  after<-getCPUTime
  stats<-getRTSStats
  putStrLn(label++" result="++show answer++" cpu_seconds="++show(fromIntegral(after-before)/1e12::Double)
    ++" max_live_bytes="++show(max_live_bytes stats)++" allocated_bytes="++show(allocated_bytes stats))
  hFlush stdout
  return answer

main=do
  let p=F.Parameters 4 8 1
      honest=F.prove p
      cs=snd(C.context p honest)
      make pr certificates=Prog(V.verifierWithContext p pr certificates)
      cmr0=progCmr(make honest cs)
      env=maybe(error "env")id(mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap cmr0)
      ic=C.initialCertificate cs;iv=C.certificateValue ic
      badInitial=cs{C.initialCertificate=ic{C.certificateValue=iv{C.initialZ=F.add F.one(C.initialZ iv)}}}
      lc=head(C.layerCertificates cs);lv=C.certificateValue lc
      badLayer=cs{C.layerCertificates=lc{C.certificateValue=lv{C.layerBeta=F.add F.one(C.layerBeta lv)}}:tail(C.layerCertificates cs)}
      q=head(F.queries honest)
      badInverse=honest{F.queries=q{F.deepInverses=(F.zero,F.zero,F.zero):tail(F.deepInverses q)}:tail(F.queries honest)}
      op=F.friOpenings q!!1;(a,b)=F.values op
      badPair=honest{F.queries=q{F.friOpenings=head(F.friOpenings q):op{F.values=(F.add F.one a,b)}:drop 2(F.friOpenings q)}:tail(F.queries honest)}
      cases=[("honest",honest,cs,True),
        ("same-CMR independently spliced initial z",honest,badInitial,False),
        ("same-CMR independently spliced FRI beta",honest,badLayer,False),
        ("same-CMR incorrect DEEP inverse",badInverse,cs,False),
        ("same-CMR altered noninitial FRI pair",badPair,cs,False)]
  phase "reference"(evaluate(F.verify p honest))
  phase "honest CMR"(evaluate cmr0)
  results<-mapM (\(name,pr,certificates,expected)->phase name $ do
    let wrapped=J.jetSubst(V.verifierWithContext p pr certificates)
        cmr=commitmentRoot(J.unwrap wrapped::CommitmentRoot () ())
        same=cmr==cmr0
        accepts=J.fastEval(J.unwrap wrapped)env()==Just()
    _<-evaluate same
    _<-evaluate accepts
    let ok=same&&accepts==expected
    _<-evaluate ok
    return(same,accepts,expected,ok)) cases
  unless(all(\(_,_,_,ok)->ok)results)exitFailure
  putStrLn "all corrected same-CMR dataflow checks pass"
