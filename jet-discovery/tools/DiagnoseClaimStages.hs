{-# LANGUAGE ScopedTypeVariables #-}
-- Diagnostic only: the actual unchanged conditional-token predicate is used.
module Main where
import Prelude hiding (drop,take)
import Control.Exception (evaluate)
import System.Environment (getArgs)
import System.Mem (performGC)
import System.IO (hFlush,stdout)
import Data.Time.Clock
import GHC.Stats
import Simplicity.Term.Core
import Simplicity.Ty (putValue)
import Simplicity.MerkleRoot (CommitmentRoot,commitmentRoot)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Types
import JetDiscovery.Run
import qualified JetDiscovery.Lib.ClaimLedger as C
import qualified JetDiscovery.Corpus.ClaimProtocols as A

say s=putStrLn s>>hFlush stdout
stage label task=do
 say ("START "++label)
 begin<-getCurrentTime
 result<-task
 end<-getCurrentTime
 performGC
 stats<-getRTSStats
 say ("END "++label++" elapsed="++show (diffUTCTime end begin)++" max_live_bytes="++show (max_live_bytes stats)++" allocated_bytes="++show (allocated_bytes stats))
 pure result
main=do
 args<-getArgs
 let mode=case args of x:_->x;_->"all"
     dummy=C.CW 0 [] [] 0 0 [] []
     canonical=progCmr (Prog (C.program A.conditionalT dummy))
 cmr<-stage "canonical whole-program jetted CMR from typed dummy witness" (evaluate (length (show canonical))>>say ("CMR "++show canonical)>>pure canonical)
 if mode=="cmr" then pure () else do
  let vector=case A.conditionalEntry of Entry _ _ _ _ _ _ _ vectors->error "use concrete conditional vectors below"
      -- conditionalEntry's existential witness is known to be CW, but avoid an
      -- unsafe cast by using the same exported constructor and a real vector.
      old=C.update [] [(0,10000),(1,6000),(2,4000),(3,4000),(4,2000),(5,3000),(6,1000)]
      new=C.update old [(14,1),(3,3000),(15,1000),(20,1000),(30,1000)]
      v=C.vectorBound cmr "complete partition1+6" A.conditionalT 16 old new 0 1000 [1,6,0] [0] 0 Nothing 0 Accept
  value<-stage "witness/signature construction with independently computed canonical CMR" $ do
   let value=C.encode (vecWitness v)
   n<-evaluate (length (filter id (putValue value)))
   say ("witness ones="++show n++" bits="++show (length (putValue value)))
   pure value
  env<-stage "actual funding/continuation environment" $ case vecEnv v cmr of Nothing->error "environment failed";Just e->evaluate e
  if mode=="fixture" then pure () else do
   wrapped<-stage "prepared pure-kernel jet substitution" $ do
    let wrapped=J.jetSubst A.conditionalT :: J.WrappedSimplicity C.Input ()
        composed=commitmentRoot (witness value>>>J.unwrap wrapped :: CommitmentRoot () ())
    equal<-evaluate (composed==cmr)
    say ("prepared composed CMR equals canonical="++show equal)
    if equal then pure wrapped else error "prepared canonical mismatch"
   stage "first positive vector actual fastEval" $ do
    accepted<-evaluate (J.fastEval (J.unwrap wrapped) env value==Just ())
    say ("complete partition actual positive="++show accepted)
    if accepted then pure () else error "positive vector rejected"
