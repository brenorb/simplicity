{-# LANGUAGE RankNTypes,GADTs #-}
-- Retention diagnostic only: full15vector correctness is recorded separately.
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import GHC.Stats(getRTSStats,gc,gcdetails_live_bytes)
import System.Mem(performGC)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import Simplicity.Bitcoin.Term(Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import qualified Simplicity.Ty.Word as Ty
import JetDiscovery.Corpus.MlDsaNtt(Poly,forwardT,inverseT)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
zeros :: Poly
zeros=case fst(bufferFill buffer511(replicate 256(w32 0)))of
 (Right p,_)->p
 _->error "full256polynomial"
forceTransform :: String -> (forall t. Simplicity t => t Poly Poly) -> IO()
forceTransform name transform=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
     answer=J.fastEval(J.unwrap(J.jetSubst transform))env zeros
 ok<-evaluate(case answer of Just p->allZero vector256 p;_->False)
 print(name,ok);unless ok(error "zero transform failed")
allZero :: Ty.Vector Word32 v -> v -> Bool
allZero SingleV x=fromWord32 x==0
allZero(DoubleV v)(a,b)=allZero v a&&allZero v b
live label=do
 performGC
 stats<-getRTSStats
 print(label,gcdetails_live_bytes(gc stats))
main=do
 hSetBuffering stdout LineBuffering
 live "baseline live bytes"
 forceTransform "forward complete256zero coefficients" forwardT
 live "after forward, transient evaluator returned"
 forceTransform "inverse complete256zero coefficients" inverseT
 live "after both, transient evaluator returned"
