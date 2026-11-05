{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.FFI.Jets as C
import Simplicity.Ty.Word(fromWord32)
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes(w32,w256ToBytes)
import JetDiscovery.Lib.ArkRefresh(entry)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
wireCheck env=canonical&&and[primitive i input|(i,input)<-zip[0..]inputs]
 where
  tx=Prim.envTx env;inputs=V.toList(sigTxIn tx)
  canonical=case parseRawTx(runPut(putNoWitnessTx tx))of
   Right raw->runPut(putNoWitnessTx(rawToSigTx raw))==runPut(putNoWitnessTx tx)
     &&and(zipWith(\a b->case(riOutpoint a,sigTxiPreviousOutpoint b)of
       (Outpoint h i,Outpoint expected j)->hashToBytes h==hashToBytes expected&&i==j)(rtIns raw)inputs)
   _->False
  primitive i input=let value=Prim.primSem Prim.InputPrevOutpoint(w32 i)env
                        actual=C.input_prev_outpoint env(w32 i)
                    in value==actual&&case(value,sigTxiPreviousOutpoint input)of
                     (Just(Right(h,j)),Outpoint expected index)->w256ToBytes h==hashToBytes expected&&fromIntegral(fromWord32 j)==index
                     _->False
check(Entry ident _ _ _ _ _ make vectors)=do
 let first=case vectors of v:_->make(vecWitness v);_->error "empty suite"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView k _)->boundEligible k;_->False
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 _<-evaluate eligible
 putStrLn("prepared_kernel_eligible="++show eligible++" CMR="++show cmr);hFlush stdout
 wires<-mapM(\v->do
   let ok=maybe False wireCheck(vecEnv v cmr)
   _<-evaluate ok
   putStrLn("wire/Haskell/C-boundary "++vecName v++" pass="++show ok);hFlush stdout
   return ok)vectors
 results<-mapM(\r->do
   _<-evaluate(vrOk r)
   putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show(vrOk r));hFlush stdout
   return(vrOk r))(runVectors make cmr vectors)
 unless(eligible&&and wires&&and results)exitFailure
 putStrLn "all current hArk completion-certificate cases pass with per-vector canonical CMR checks"
main=entry>>=check
