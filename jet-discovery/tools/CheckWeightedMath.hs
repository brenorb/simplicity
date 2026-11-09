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
import qualified JetDiscovery.Lib.WeightedMath as W
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
main=do
 let encodeSwap (a,b,d,q)=((w64 a,w64 b),(w64 d,w64 q))
     swapCases=[(500000,500000,0,10000),(500000,500000,1,10000),(600000,400000,0,100000)]
     joinCases=[(0,0,500000,500000,0),(500000,500000,10000,10000,999998),(500000,500000,100000,0,999998)]
     encodeJoin (a,b,x,y,s)=((w64 a,w64 b),((w64 x,w64 y),w64 s))
 a<-run "weighted exact-in" W.swapInRef ([(show q,encodeSwap q,let (x,y)=W.swapInInteger a b d n in (w64 x,w64 y),Accept)|q@(a,b,d,n)<-swapCases]++[("max-in ratio",encodeSwap (500000,500000,0,200000),(w64 0,w64 0),Reject)])
 b<-run "weighted exact-out" W.swapOutRef ([(show q,encodeSwap q,let (x,y)=W.swapOutInteger a b d n in (w64 x,w64 y),Accept)|q@(a,b,d,n)<-swapCases]++[("max-out ratio",encodeSwap (500000,500000,0,200000),(w64 0,w64 0),Reject)])
 c<-run "weighted invariant" W.invariantRef [(show (a,b),(w64 a,w64 b),w64 (W.invariantInteger a b),Accept)|(a,b)<-[(500000,500000),(600000,400000),(1,1000000)]]
 d<-run "weighted LP join" W.joinRef [(show q,encodeJoin q,w64 (W.joinInteger a b x y n),Accept)|q@(a,b,x,y,n)<-joinCases]
 unless (a&&b&&c&&d) exitFailure
