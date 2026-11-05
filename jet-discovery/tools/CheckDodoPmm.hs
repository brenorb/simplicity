{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Ty.Word (toBit)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.DodoMath as D
import qualified JetDiscovery.Lib.DodoPmm as P
import qualified JetDiscovery.Corpus.NativePmmPool as A
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx

check :: (Simplicity t,Primitive t) => t (P.Input,P.Output) ()
check=(take A.pmmQuote&&&ih)>>>eq>>>verify
encode ([b,q,b0,q0,r,i],baseIn,pay,(receipt,bt,qt,newR))=(((w64 b,(w64 q,(w64 b0,(w64 q0,(w64 r,w64 i))))),(toBit baseIn,w64 pay)),(w64 receipt,(w64 bt,(w64 qt,w64 newR))))
encode _=error "six PMM state fields"
env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
main=do
 let initial=[1000000,1000000,1000000,1000000,0,D.one]
     apply s baseIn pay=let (receipt,bt,qt,r)=P.quoteInteger s baseIn pay in [s!!0+(if baseIn then pay else negate receipt),s!!1+(if baseIn then negate receipt else pay),bt,qt,r,s!!5]
     above=apply initial False 40000
     below=apply initial True 30000
     backBase=D.targetInteger (above!!0) (above!!1-above!!3) (D.one*D.one `div`(above!!5))-above!!0
     backQuote=D.targetInteger (below!!1) (below!!0-below!!2) (below!!5)-below!!1
     cases=[("ONE base",initial,True,30000),("ONE quote",initial,False,40000),("ABOVE quote",above,False,10000),("BELOW base",below,True,10000),("ABOVE integral",above,True,backBase `div`2),("ABOVE exact",above,True,backBase),("ABOVE cross",above,True,backBase+10000),("BELOW integral",below,False,backQuote `div`2),("BELOW exact",below,False,backQuote),("BELOW cross",below,False,backQuote+10000),("nonunit price",[1000000,1000000,1000000,1000000,0,12*10^17],True,15000)]
     quote=P.quoteInteger initial True 30000
     (receipt,bt,qt,r)=quote
     vectors=[Vector name env (s,baseIn,pay,P.quoteInteger s baseIn pay) Accept|(name,s,baseIn,pay)<-cases]++[Vector "wrong receipt" env (initial,True,30000,(receipt+1,bt,qt,r)) Reject,Vector "wrong stored target" env (initial,True,30000,(receipt,bt+1,qt,r)) Reject,Vector "wrong R" env (initial,True,30000,(receipt,bt,qt,0)) Reject]
     program=boundProgram check . encode
     cmr=progCmr (program (vecWitness (head vectors)))
 putStrLn "DODO complete PMM regimes START";hFlush stdout
 oks<-forM (runVectors program cmr vectors) $ \row->do
  putStrLn (vrName row++"\t"++show (vrOk row)++"\t"++vrNote row);hFlush stdout
  pure (vrOk row)
 putStrLn ("DODO PMM "++show (length oks)++" vectors "++if and oks then "PASS" else "FAIL")
 unless (and oks) exitFailure
