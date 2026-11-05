{-# LANGUAGE RankNTypes,GADTs #-}
-- Exact unsigned-branch relation reproducer, not a claimed full-sale run.
-- Two genuine identical escrow inputs otherwise share one payout. CurrentIndex
-- must be0so at most one protected state input can satisfy the allocation.
module Main where
import Prelude hiding(drop,take,not,and,or)
import Control.Monad(forM_,unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Corpus.FairSwap(stateT,hash32)
import JetDiscovery.Lib.State
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVector,vrOk,vrNote)
import qualified JetDiscovery.Ref.FairSwap as R
import qualified JetDiscovery.Ref.Bip340 as Bip
type Header=(Word256,(Word256,Word256))
type Input=(Header,Word256)
key=Bip.bytesFromInt 991
chunks=[Bip.bytesFromInt i|i<-[10..13]]
header=R.header key chunks
pack(a,(b,c))=(w256FromBytes a,(w256FromBytes b,w256FromBytes c))
same a b=(a&&&b)>>>eq>>>verify
branch :: Bool -> Bool -> Input -> Prog
branch indexed revealed=boundProgram kernel
 where
  kernel :: forall t. (Simplicity t,Primitive t) => t Input ()
  kernel=(index&&&same(unit>>>Tx.numInputs)(konst(w32 2))&&&
    same(unit>>>Tx.numOutputs)(konst(w32 1))&&&same(unit>>>Tx.currentValue)(konst(w64 100000))&&&
    loadState((oh&&&actualKey)>>>stateT(if revealed then 1 else 0))&&&keyCheck&&&
    (konst(w16 10)>>>TL.checkLockDistance)&&&
    same(konst(w32 0)>>>primitive P.OutputValue>>>verify)(konst(w64 100000))&&&
    same(konst(w32 0)>>>primitive P.OutputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 destination)))))>>>unit
  index :: forall t. (Simplicity t,Primitive t) => t Input ()
  index=if indexed then same(unit>>>primitive P.CurrentIndex)(konst(w32 0))else unit
  actualKey :: forall t. Core t => t Input Word256
  actualKey=if revealed then ih else konst(w256 0)
  keyCheck :: forall t. Simplicity t => t Input ()
  keyCheck=if revealed then same(ih>>>hash32)(ooh)else unit
  destination=unhex "5120"<>Bip.bytesFromInt(Bip.pubkeyOf(if revealed then 17 else 29))
environment revealed index cmr=mkEnv transaction index(\_->stateTap cmr oldState)cmr
 where
  oldState=R.stateBytes(if revealed then 1 else 0)header(if revealed then key else B.replicate 32 0)
  script=BL.fromStrict(stateScript cmr oldState)
  destination=unhex "5120"<>Bip.bytesFromInt(Bip.pubkeyOf(if revealed then 17 else 29))
  transaction=mkTx 2[mkInput(dummyOutpoint 0)100000 script 10,mkInput(dummyOutpoint 1)100000 script 10]
   [mkOutput 100000 destination]0
main=do
 hSetBuffering stdout LineBuffering
 forM_[False,True]$ \revealed->forM_[False,True]$ \indexed->do
  let program=branch indexed revealed
      input=(pack header,w256FromBytes(if revealed then key else B.replicate 32 0))
      cmr=progCmr(program input)
  forM_[0,1]$ \index->do
   let expected=if indexed&&index/=0 then Reject else Accept
       result=runVector program cmr(Vector "duplicate collateral timeout"(environment revealed index)input expected)
   print("revealed",revealed,"fixed index guard",indexed,"current index",index,vrOk result,vrNote result)
   unless(vrOk result)(error "unsigned timeout index relation failed")
