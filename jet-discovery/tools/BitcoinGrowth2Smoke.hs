{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(unless)
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.FFI.Jets as CJet
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.DataTypes
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Ty.Word(fromWord32)
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes(w32,w256ToBytes)
import qualified JetDiscovery.Ref.Bip340 as EC
import qualified JetDiscovery.Ref.SilentPayment as Silent
import JetDiscovery.Corpus.BitcoinGrowth2(entries)
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import System.Environment(getArgs)
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
powm _ 0 _=1
powm a e m|even e=let x=powm a(e`div`2)m in x*x`mod`m
           |otherwise=a*powm a(e-1)m`mod`m
decodeDer der
 |B.length der/=70||B.take 2 der/=B.pack[0x30,68]=Nothing
 |otherwise=do
  (r,next)<-integer 2
  (s,end)<-integer next
  if end==70&&r>0&&r<EC.n&&s>0&&s<=EC.n`div`2 then Just(r,s)else Nothing
 where
  integer offset
   |offset+2>B.length der||B.index der offset/=2=Nothing
   |otherwise=let n=fromIntegral(B.index der(offset+1));bytes=B.take n(B.drop(offset+2)der)
              in if n==0||B.length bytes/=n||B.head bytes>=128||(n>1&&B.head bytes==0&&B.index bytes 1<128)
                 then Nothing else Just(EC.intFromBytes bytes,offset+2+n)
wireCheck ident env=canonical&&cBoundary&&legacy
 where
  tx=Prim.envTx env;inputs=V.toList(sigTxIn tx)
  canonical=case parseRawTx(runPut(putNoWitnessTx tx))of
   Right raw->and(zipWith(\a b->case(riOutpoint a,sigTxiPreviousOutpoint b)of
       (Outpoint h i,Outpoint actual j)->hashToBytes h==hashToBytes actual&&i==j)(rtIns raw)inputs)
   _->False
  cBoundary=and[case(CJet.input_prev_outpoint env(w32(toInteger i)),sigTxiPreviousOutpoint input)of
    (Just(Right(h,j)),Outpoint expected index)->w256ToBytes h==hashToBytes expected&&fromIntegral(fromWord32 j)==index
    _->False|(i,input)<-zip[0..]inputs]
  legacy|ident/="app-silent-payment-output-covenant"=True
        |length inputs/=2=False
        |otherwise=let input=inputs!!1;ss=BL.toStrict(sigTxiScriptSig input)
                   in B.length ss==106&&B.head ss==71&&B.index ss 71==1&&B.index ss 72==33&&case decodeDer(B.take 70(B.drop 1 ss))of
                    Nothing->False
                    Just(r,s)->let public=Silent.decodeCompressed(B.drop 73 ss)
                                   script=BL.toStrict(sigTxiScript input)
                                   message=Silent.legacySighash tx script
                                   inv=powm s(EC.n-2)EC.n
                                   point=EC.pointAdd(EC.pointMul EC.gPt(EC.intFromBytes message*inv`mod`EC.n))(EC.pointMul public(r*inv`mod`EC.n))
                               in public/=Nothing&&script==Silent.p2pkhScript public&&point/=Nothing&&EC.xOnly point`mod`EC.n==r
check(Entry ident _ _ _ _ _ make vectors)=do
 putStrLn(ident++" vectors="++show(length vectors));hFlush stdout
 let first=case vectors of v:_->make(vecWitness v);_->error "empty vector suite"
     baseline=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
 _<-evaluate eligible
 putStrLn("  prepared_kernel_eligible="++show eligible++" canonical_raw_wire_primitive_boundary=True");hFlush stdout
 wire<-mapM(\v->do
   let ok=maybe False(wireCheck ident)(vecEnv v baseline)
   _<-evaluate ok
   putStrLn("  wire/C-boundary"++(if ident=="app-silent-payment-output-covenant"then"/actual-legacy-ECDSA"else"")++" "++vecName v++" pass="++show ok);hFlush stdout
   return ok)vectors
 results<-mapM(\result->do
  _<-evaluate(vrOk result)
  putStrLn("  "++vrName result++" expected="++show(vrExpect result)++" actual="++vrNote result++" pass="++show(vrOk result));hFlush stdout
  return(vrOk result))(runVectors make baseline vectors)
 putStrLn("  CMR="++show baseline);hFlush stdout
 return(eligible&&and wire&&and results)
main=do
 programs<-entries;filters<-getArgs
 let selected=if null filters then programs else filter(\e->entryId e `elem` filters)programs
 unless(not(null selected))exitFailure
 outcomes<-mapM check selected
 unless(and outcomes)exitFailure
 putStrLn "all BitcoinGrowth2 vectors pass with stable CMR"
