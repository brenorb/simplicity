module Main where
import Control.Monad (unless)
import System.Environment (getArgs)
import qualified JetDiscovery.Corpus.EprintExpansion as E
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Types
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Term.Core (witness,(>>>))
import Simplicity.Ty.Word
import Simplicity.Digest (hash0)
point (Just(x,y))=(toWord256 x,toWord256 y)
point Nothing=error "fixture point"
program z=Prog (witness ((point R.gPt,(point (R.pointMul R.gPt (R.n-1)),point (R.pointMul R.gPt 5))),((toWord256 1,toWord256 7),(toWord256 3,toWord256 z))) >>> E.frostShareT)
main=do
 args<-getArgs
 let env=maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)
     eval p=J.fastEval (J.unwrap (J.jetSubst (unProg p))) env ()==Just ()
     same=progCmr (program 105)==progCmr (program 106)
     good=eval (program 105);bad=eval (program 106)
     expected=args/=["before"]
 print (same,good,bad)
 unless (same && good==expected && not bad) (error "FROST identity commitment regression")
