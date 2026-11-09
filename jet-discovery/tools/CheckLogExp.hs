{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.LogExpBounded as L
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx

env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
run :: forall a b. (TyC a,TyC b) => String -> (forall t. Simplicity t => t a b) -> [(String,a,b,Expect)] -> IO Bool
run label f rows=do
 let program=boundProgram (((take f)&&&ih)>>>eq>>>verify)
     vectors=[Vector name env (input,expected) verdict|(name,input,expected,verdict)<-rows]
     cmr=progCmr (program (vecWitness (head vectors)))
     results=runVectors program cmr vectors
 flags<-forM results $ \r->do
  putStrLn (label++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)
  hFlush stdout
  pure (vrOk r)
 pure (and flags)
signed x=(toBit (x<0),toWord128 (abs x))
roundPow up x y
 |y==L.ones=x
 |y==2*L.ones=rounded x x
 |y==4*L.ones=let q=rounded x x in rounded q q
 |otherwise=let raw=L.powInteger x y;err=(raw*10000+L.ones-1) `div`L.ones+1 in if up then raw+err else max 0 (raw-err)
 where rounded a b=if up then (a*b+L.ones-1) `div`L.ones else a*b `div`L.ones
main=do
 a<-run "Balancer ln" L.lnRefT ([(show x,toWord128 x,signed (L.lnInteger x),Accept)|x<-[1,7*10^17,9*10^17,10^18,101*10^16,11*10^17,3*10^18]]++[("zero logarithm argument",toWord128 0,signed 0,Reject),("altered negative logarithm",toWord128 (7*10^17),signed (L.lnInteger (7*10^17)-1),Reject)])
 b<-run "Balancer exp" L.expRefT ([(show x,signed x,toWord128 (L.expInteger x),Accept)|x<-[-41*10^18,-2*10^18,-10^18,0,10^18,3*10^18,41*10^18]]++[("outside bounded exp domain",signed (41*10^18+1),toWord128 0,Reject)])
 let pairs=[(500000,8*10^17),(500000,2*10^17),(77*10^16,4*10^18),(102*10^16,8*10^17),(98*10^16,2*10^17),(3*10^18,4*10^18),(0,0),(0,2*10^17)]
 c<-run "Balancer raw pow" L.powRefT ([(show (x,y),(toWord128 x,w64 y),toWord128 (L.powInteger x y),Accept)|(x,y)<-pairs]++[("natural product below source minimum",(toWord128 1,w64 (4*10^18)),toWord128 0,Reject)])
 d<-run "FixedPoint powDown" L.powDown [(show (x,y),(toWord128 x,w64 y),toWord128 (roundPow False x y),Accept)|(x,y)<-pairs++[(102*10^16,10^18),(102*10^16,2*10^18)]]
 e<-run "FixedPoint powUp" L.powUp [(show (x,y),(toWord128 x,w64 y),toWord128 (roundPow True x y),Accept)|(x,y)<-pairs++[(102*10^16,10^18),(102*10^16,2*10^18)]]
 unless (a&&b&&c&&d&&e) exitFailure
