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
import qualified JetDiscovery.Lib.PendleMath as P
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
base sy pt i rem rate=(w64 sy,(w64 pt,(w64 i,(w64 rem,w64 rate))))
out (sy,pt,net,fee,res,lnr)=(w64 sy,(w64 pt,(((toBit (net<0),w64 (abs net)),(w64 fee,w64 res)),w64 lnr)))
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
main=do
 args<-getArgs
 let want x=null args||x `elem`args
     one=P.scale;yr=P.year
     firstCases=[(1000000,1000000,one,yr),(1000000,1200000,12*10^17,yr),(1000000,900000,one,yr `div`2),(1000000,1100000,one,yr `div`3),(10^9,10^9,one,yr)]
     first=P.initialRateInteger 1000000 1000000 one yr
     firstRows=[(show (sy,pt,i,rem),base sy pt i rem 0,w64 (P.initialRateInteger sy pt i rem),Accept)|(sy,pt,i,rem)<-firstCases]++[("altered initial rate",base 1000000 1000000 one yr 0,w64 (first+1),Reject),("expired initial liquidity",base 1000000 1000000 one 0 0,w64 0,Reject),("initial annual rate outside bound",base 1000000 1000000 one (yr `div`100) 0,w64 0,Reject)]
     buyCase=P.tradeInteger 1000000 1000000 one yr first True 10000
     (afterSy,afterPt,_,_,_,afterRate)=buyCase
     tradeCases=[(1000000,1000000,one,yr,first,True,10000),(1000000,1000000,one,yr,first,False,10000),(1000000,1200000,12*10^17,yr,first,True,10000),(1000000,1200000,12*10^17,yr,first,False,10000),(afterSy,afterPt,one,yr `div`2,afterRate,False,5000),(afterSy,afterPt,11*10^17,yr `div`3,afterRate,True,7000),(10^9-100000,10^9-100000,one,yr,first,False,10000)]
     (sy,pt,net,fee,res,rate)=buyCase
     input=(base 1000000 1000000 one yr first,(toBit True,w64 10000))
     tradeRows=[(show (s,p,i,rem,r,b,q),(base s p i rem r,(toBit b,w64 q)),out (P.tradeInteger s p i rem r b q),Accept)|(s,p,i,rem,r,b,q)<-tradeCases]++[("altered reserve fee",input,out (sy,pt,net,fee,res+1,rate),Reject),("altered successor implied rate",input,out (sy,pt,net,fee,res,rate+1),Reject),("buy cannot consume whole PT reserve",(base 1000000 1000000 one yr first,(toBit True,w64 1000000)),out buyCase,Reject),("buy post-fee exchange below1",(base 1000000 1000000 one yr (2*10^16),(toBit True,w64 1000)),out buyCase,Reject),("expired trade",(base 1000000 1000000 one 0 first,(toBit True,w64 10000)),out buyCase,Reject),("unsupported proportion",(base 1000000 100000000 one yr first,(toBit False,w64 10000)),out buyCase,Reject),("zero PY index",(base 1000000 1000000 0 yr first,(toBit True,w64 10000)),out buyCase,Reject)]
 a<-if want "initial" then run "Pendle initial annual rate" P.initialRate firstRows else pure True
 b<-if want "trade" then run "Pendle complete quote and successor" P.trade tradeRows else pure True
 unless (a&&b) exitFailure
