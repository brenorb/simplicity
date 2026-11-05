{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Corpus.ContractMath as T
import qualified JetDiscovery.Lib.V3BoundedMath as V
import qualified JetDiscovery.Lib.V3FiniteSwap as F
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
check :: (Simplicity t,Primitive t,TyC a,TyC b) => t a b -> t (a,b) ()
check f=(take f&&&ih)>>>eq>>>verify
run :: (TyC a,TyC b) => String -> (forall t. (Simplicity t,Primitive t)=>t a b) -> [(String,a,b,Expect)] -> IO Bool
run label term rows=do
 let program=boundProgram (check term)
     vectors=[Vector name env (input,expected) ex|(name,input,expected,ex)<-rows]
     cmr=progCmr (program (vecWitness (head vectors)))
 putStrLn (label++" START");hFlush stdout
 oks<-forM (runVectors program cmr vectors) $ \r->do
  putStrLn (label++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r);hFlush stdout
  pure (vrOk r)
 putStrLn (label++" "++show (length oks)++" vectors "++if and oks then "PASS" else "FAIL");hFlush stdout
 pure (and oks)
lpInput p left up l=(toWord128 p,((toBit left,toBit up),w64 l))
lpOut (a,b)=(w64 a,w64 b)
stepInput p t l i a=((toWord128 p,toWord128 t),(w64 l,(toBit i,w64 a)))
stepOut (p,i,o,f)=(toWord128 p,(w64 i,(w64 o,w64 f)))
fillInput p t l0 l1 left i a=((toWord128 p,toWord128 t),((w64 l0,w64 l1),(toBit left,(toBit i,w64 a))))
fillOut (p,l,i,o,g0,g1)=(toWord128 p,(toBit l,(w64 i,(w64 o,(toWord128 g0,toWord128 g1)))))
main=do
 args<-getArgs
 let want x=null args||x `elem`args
     midL=78990846045029531151608375686;midR=79466191966197645195421774833
     tickCases=[(-120,F.lower),(-60,midL),(0,V.q96),(60,midR),(120,F.upper)]
     lpCases=[(p,l,u,n)|p<-[midL,V.q96,midR],l<-[False,True],u<-[False,True],let n=100000000]
     stepCases=[(p,t,l,i,a)|(p,t)<-[(midL,midR),(midR,midL)],i<-[False,True],a<-[10000,10000000],let l=100000000]++[(midL,midR,0,True,100000),(midR,midL,0,False,100000),(midL,midR,100000000,True,1),(V.q96,V.q96,100000000,True,10000)]
     fullCases=[(midL,midR,100000000,200000000,True,True,1000000),(midR,midL,100000000,200000000,False,True,800000),(midL,midR,100000000,200000000,True,False,600000),(midR,midL,100000000,200000000,False,False,100000),(midL,V.q96,100000000,200000000,True,True,1000000),(V.q96,midL,100000000,200000000,False,True,100000),(midL,midR,0,200000000,True,True,100000),(V.q96,midR,100000000,200000000,True,True,100000)]
     (p1,i1,o1,f1)=V.stepInteger midL midR 100000000 True 10000
     (p2,l2,i2,o2,g0,g1)=F.fillInteger midL midR 100000000 200000000 True True 1000000
 a<-if want "ticks" then run "V3 pinned tick bounds" T.tickSqrt ([(show t,(toBit (t<0),w32 (abs t)),w256 p,Accept)|(t,p)<-tickCases]++[("altered tick120",(toBit False,w32 120),w256 (F.upper+1),Reject)]) else pure True
 b<-if want "lp" then run "V3 exact LP amount deltas" F.lpAmounts ([(show (p,l,u,n),lpInput p l u n,lpOut (F.lpInteger p l u n),Accept)|(p,l,u,n)<-lpCases]++[("altered mint",lpInput midL True True 100000000,let (x,y)=F.lpInteger midL True True 100000000 in lpOut (x-1,y),Reject),("liquidity outside bound",lpInput midL True False (10^9+1),lpOut (0,0),Reject)]) else pure True
 c<-if want "step" then run "V3 exact SwapMath step" V.swapStep ([(show (p,t,l,i,a),stepInput p t l i a,stepOut (V.stepInteger p t l i a),Accept)|(p,t,l,i,a)<-stepCases]++[("altered fee",stepInput midL midR 100000000 True 10000,stepOut (p1,i1,o1,f1+1),Reject),("out-of-domain current price",stepInput (V.q96*9 `div`10) midR 100000000 True 10000,stepOut (p1,i1,o1,f1),Reject)]) else pure True
 d<-if want "fill" then run "V3 finite crossing and fee allocation" F.fill ([(show (p,t,a,b,l,i,q),fillInput p t a b l i q,fillOut (F.fillInteger p t a b l i q),Accept)|(p,t,a,b,l,i,q)<-fullCases]++[("wrong crossed fee band",fillInput midL midR 100000000 200000000 True True 1000000,fillOut (p2,l2,i2,o2,g1,g0),Reject),("wrong old side",fillInput midL midR 100000000 200000000 False True 1000000,fillOut (p2,l2,i2,o2,g0,g1),Reject),("unsupported outer endpoint",fillInput midL F.upper 100000000 200000000 True True 1000000,fillOut (p2,l2,i2,o2,g0,g1),Reject)]) else pure True
 e<-if want "fees" then run "V3 Q128 fee growth" V.feeGrowth ([(show (f,l),(w64 f,w64 l),toWord128 (if f==0 then 0 else f*V.q128 `div`l),Accept)|(f,l)<-[(0,0),(1,1000),(333,100000000),(1000,200000000)]]++[("growth width overflow",(w64 1,w64 1),toWord128 0,Reject),("nonzero fee no liquidity",(w64 1,w64 0),toWord128 0,Reject)]) else pure True
 unless (a&&b&&c&&d&&e) exitFailure
