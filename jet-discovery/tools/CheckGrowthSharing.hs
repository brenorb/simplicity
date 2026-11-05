{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
module Main where
import Control.Monad (unless)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.MerkleRoot (CommitmentRoot,commitmentRoot)
import Simplicity.Digest (Hash256)
import Simplicity.Ty.Word (vector256)
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Dag as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Serialization.BitString as B
import JetDiscovery.Cost (TermWeight,milliWeigh)
import JetDiscovery.JetSets (PrimOnly,Ablate,NoSha256)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Corpus.ContractGrowth as G
import qualified JetDiscovery.Corpus.ContractMessageApps as M
import qualified JetDiscovery.Corpus.ContractBridge as V

type Pure a b=forall t. Simplicity t => t a b
main :: IO ()
main=do
 args<-getArgs
 let cases=
       [("state hash",check "state hash" G.stateHashRef G.stateHashWrapped (G.ledger [100003,70000,40000,30000,4])),
        ("full128 numerator ratio",check "full128 numerator ratio" G.ratioRef G.ratioWrapped ((w64 1000,w64 70001),w64 100004)),
        ("Permit2 token permissions",check "Permit2 token permissions" M.pTokenRef M.pTokenWrapped (w256 1000)),
        ("Permit2 native recipient witness",check "Permit2 native recipient witness" M.pWitnessRef M.pWitnessWrapped (w256 123)),
        ("Permit2 struct",check "Permit2 struct" M.pStructRef M.pStructWrapped ((w256 5,w256 2000000000),(w256 1,w256 2))),
        ("EIP712 envelope",check "EIP712 envelope" M.pEnvelopeRef M.pEnvelopeWrapped (w256 3)),
        ("BubblegumV1 leaf",check "BubblegumV1 leaf" M.bLeafRefT M.bLeafWrapped (w256 1,(w256 2,w64 7))),
        ("Keccak tree node",check "Keccak tree node" M.keccakNode M.keccakNodeWrapped (Left (),(w256 3,w256 4))),
        ("VAA full184-byte body",check "VAA full184-byte body" V.bodyHashRef V.bodyHashWrapped (V.packV vector256 (replicate 256 (w8 0)))) ,
        ("sealed commitment",check "sealed commitment" G.blindCommitRef G.blindCommitWrapped (w64 1200,(w256 333,w8 0)))]
 rs<-sequence [action|(name,action)<-cases,null args||name `elem` args]
 unless (and rs) exitFailure

check :: forall a b. (TyC a,TyC b) => String -> Pure a b -> J.WrappedSimplicity a b -> a -> IO Bool
check name raw wrapped inputValue=do
 let cached :: Pure a b
     cached=J.unwrap wrapped
     cmr :: Pure a b -> Hash256
     cmr t=commitmentRoot (J.unwrap (J.jetSubst t)::CommitmentRoot a b)
     normal :: Pure a b -> Integer
     normal t=milliWeigh (J.unwrap (J.jetSubst t)::TermWeight a b)
     baseline :: Pure a b -> Integer
     baseline t=milliWeigh (J.unwrap (D.jetSubst (t::D.JetDag PrimOnly a b))::TermWeight a b)
     noSha :: Pure a b -> Integer
     noSha t=milliWeigh (J.unwrap (D.jetSubst (t::D.JetDag (Ablate NoSha256) a b))::TermWeight a b)
     wire :: Pure a b -> (Maybe [Bool],[Bool])
     wire t=let d=D.jetDag ((witness inputValue>>>t>>>unit)::D.JetDag J.JetType () ()) in (B.putWitnessData d,B.putDagNoWitnessLengthCode d)
     sameCmr=cmr raw==cmr cached
 say (name++": final jetted CMR preserved="++show sameCmr)
 let nc=(normal raw,normal cached)
 say (name++": normal milliWU="++show nc)
 let bc=(baseline raw,baseline cached)
 say (name++": primitive-only milliWU="++show bc)
 let ac=(noSha raw,noSha cached)
 say (name++": noSHA milliWU="++show ac)
 let bits=wire raw==wire cached
 say (name++": exact encoded program/witness bits preserved="++show bits)
 let ok=sameCmr&&uncurry (==) nc&&uncurry (==) bc&&uncurry (==) ac&&bits
 say (name++": PASS="++show ok)
 pure ok
 where say s=putStrLn s>>hFlush stdout
