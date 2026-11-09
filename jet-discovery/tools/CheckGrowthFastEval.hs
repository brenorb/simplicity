{-# LANGUAGE RankNTypes #-}
-- Additional functional path, not a substitute for Run.runVector CMR checks.
module Main where
import Prelude hiding (drop,take,fail)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core hiding (sum)
import Simplicity.Bitcoin.Term (Simplicity,Primitive(..),Jet(..))
import Simplicity.MerkleRoot (CommitmentRoot,commitmentRoot)
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Types
import JetDiscovery.Run (runVector,vrOk)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import qualified JetDiscovery.Corpus.ContractMessageApps as M
import qualified JetDiscovery.Corpus.ContractBridge as V

-- Every combinator, including unselected branches, contributes. Jet specs
-- cannot contain Witness or Delegate by the Jet class's rank2 constraint.
data Audit a b=Audit Integer Bool
join (Audit a d) (Audit b e)=Audit (a+b) (d||e)
unary (Audit a d)=Audit a d
instance Core Audit where
 iden=Audit 0 False
 comp=join
 unit=Audit 0 False
 injl=unary
 injr=unary
 match=join
 pair=join
 take=unary
 drop=unary
instance Assert Audit where
 assertl a _=unary a
 assertr _ a=unary a
 fail _=Audit 0 False
instance Witness Audit where witness _=Audit 1 False
instance Delegate Audit where disconnect _ _=Audit 0 True
instance Primitive Audit where primitive _=Audit 0 False
instance Jet Audit where jet _ _=Audit 0 False
instance Simplicity Audit

main :: IO ()
main=do
 args<-getArgs
 let entries=G.entries++M.entries++V.entries
     selected=[e|e@(Entry ident _ _ _ _ _ _ _)<-entries,null args||ident `elem` args]
 result<-forM selected $ \(Entry ident _ _ _ _ _ program vectors)->do
  let first=case vectors of v:_->v;_->error "empty growth vectors"
      firstProg=program (vecWitness first)
      wrapped=J.jetSubst (unProg firstProg)
      canonical=commitmentRoot (J.unwrap wrapped::CommitmentRoot () ())
      rawCmr0=commitmentRoot (unProg firstProg::CommitmentRoot () ())
      canonicalFirst=case vecEnv first canonical of
       Just env->(J.fastEval (J.unwrap wrapped) env ()==Just ())==(vecExpect first==Accept)
       Nothing->False
  say (ident++" canonical jetted first vector="++show canonicalFirst)
  outcomes<-forM vectors $ \v->do
   let p=program (vecWitness v)
       Audit wc delegates=unProg p
       shape=wc==1&&not delegates
       invariant=commitmentRoot (unProg p::CommitmentRoot () ())==rawCmr0
       accepted=case vecEnv v canonical of
        Nothing->False
        Just env->(J.fastEval (unProg p::J.FastEval J.JetType () ()) env ()==Just ())==(vecExpect v==Accept)
       ok=canonicalFirst&&shape&&invariant&&accepted
   say (ident++"\t"++vecName v++"\tfunctional="++show accepted++"\trawCMR="++show invariant++"\tsingleWitness/noDisconnect="++show shape)
   pure ok
  -- One additional negative is independently run through the canonical
  -- jetSubst/fastEval path; all others retain the ordinary background driver.
  negative<-case [v|v<-vectors,vecExpect v==Reject] of
   v:_->pure (vrOk (runVector program canonical v))
   []->pure False
  let ok=canonicalFirst&&negative&&and outcomes
  say (ident++": "++show (length outcomes)++" functional vectors; canonical first+/negative="++show negative++"; PASS="++show ok)
  pure (length outcomes,ok)
 say ("TOTAL: "++show (length result)++" groups, "++show (sum (map fst result))++" functional vectors, "++show (length (filter (not . snd) result))++" failed groups")
 unless (all snd result) exitFailure
 where say s=putStrLn s>>hFlush stdout
