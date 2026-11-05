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
import qualified JetDiscovery.Corpus.ContractExpansion as C
import qualified JetDiscovery.Lib.Ecrecover as E

type Pure a b=forall t. Simplicity t => t a b
main :: IO ()
main=do
 let action=check "ecrecover minimal pure operands" C.ecRecover E.recoverWrapped (w256 5,(w256 3,(w256 4,Left ())))
 result<-action
 unless result exitFailure

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
 let ac=(noSha raw,noSha cached)
 say (name++": noSHA milliWU="++show ac)
 let bits=wire raw==wire cached
 say (name++": exact encoded program/witness bits preserved="++show bits)
 let bc=(baseline raw,baseline cached)
 say (name++": primitive-only milliWU="++show bc)
 let ok=sameCmr&&uncurry (==) nc&&uncurry (==) bc&&uncurry (==) ac&&bits
 say (name++": PASS="++show ok)
 pure ok
 where say s=putStrLn s>>hFlush stdout
