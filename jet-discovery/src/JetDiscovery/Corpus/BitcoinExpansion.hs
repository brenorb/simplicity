{-# LANGUAGE RankNTypes #-}
-- | Complete bounded spend conditions, with transaction-bound signatures,
-- timelocks, preimage checks and payout covenants. Off-chain setup is outside
-- each program's scope; the entries do not claim to implement entire protocols.
module JetDiscovery.Corpus.BitcoinExpansion (entries) where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Word as DW
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg,checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R

type SigW=(Word256,Word256)
type SpendW=(Integer,Word256,[Maybe SigW])
type Input=(Word8,(Word256,Vector8 (Either () SigW)))
pick False=take
pick True=drop
at8 i=pick (i>=4) (pick (i`mod`4>=2) (pick (odd i) iden))
mk8v [a,b,c,d,e,f,g,h]=(((a,b),(c,d)),((e,f),(g,h)))
mk8v _=error "eight slots"
data Guard=Signed Int|Threshold Integer [Int]|Absolute Integer|AbsoluteTime Integer|Relative Integer|Hashlock|Count Integer|Pay Integer Int Integer|Same Integer|Remain Integer Integer|Oracle Integer deriving Show
data App=App String String String [String] [(Integer,[Guard])] [Scenario]
data Scenario=Scenario String Integer DW.Word32 DW.Word32 [(Integer,BS.ByteString)] [Int] BS.ByteString Expect
keys=[11,22,33,44,55] :: [Integer]
pk i=w256 (R.pubkeyOf (keys!!i))
ourScript=unhex "5120"<>BS.replicate 32 0xa1
recipient i=unhex "0014"<>BS.replicate 20 (fromIntegral (0xb0+i))
scriptHash=w256FromBytes . hashToBytes . sha256
preimage=BS.replicate 32 0xab
preHash=w256FromBytes (hashToBytes (sha256 preimage))
attMsg o=R.taggedHash "Simplicity/DLC/Enumerated" (BS.replicate 32 0xee<>BS.singleton (fromInteger o))

program :: (Simplicity t,Primitive t) => [(Integer,[Guard])] -> SpendW -> t () ()
program branches (mode,secret,sigs)=witness encoded>>>programT branches
 where
  encoded :: Input
  encoded=(w8 mode,(secret,mk8v (map (maybe (Left ()) Right) (sigs++replicate 3 Nothing))))

programT :: (Simplicity t,Primitive t) => [(Integer,[Guard])] -> t Input ()
programT branches=L.foldr branch failure branches
 where
  branch (m,gs) rest=(oh&&&konst (w8 m)>>>eq)&&&iden>>>cond (L.foldl' (\a b->(a&&&guard b)>>>unit) unit gs) rest
  sigAt i=drop (drop (at8 i))
  signed i=(((konst (pk i)&&&(unit>>>sigMsg))&&&(sigAt i>>>verify))>>>Secp.bip_0340_verify)
  optional i=sigAt i&&&(unit>>>sigMsg)>>>match (konst (w8 0)) (checkSigWith (pk i) ih oh>>>konst (w8 1))
  guard (Signed i)=signed i
  guard (Threshold k is)=(konst (w8 k)&&&L.foldl' (\x i->(x&&&optional i)>>>A.add word8>>>ih) (konst (w8 0)) is)>>>A.le word8>>>verify
  guard (Absolute n)=konst (w32 n)>>>TL.checkLockHeight
  guard (AbsoluteTime n)=konst (w32 n)>>>TL.checkLockTime
  guard (Relative n)=konst (w16 n)>>>TL.checkLockDistance
  guard Hashlock=((unit>>>ctx8Init)&&&ioh>>>ctx8Add32>>>ctx8Finalize)&&&konst preHash>>>eq>>>verify
  guard (Count n)=((unit>>>Tx.numOutputs)&&&konst (w32 n))>>>eq>>>verify
  guard (Pay i dest amount)=((konst (w32 i)>>>primitive Prim.OutputScriptHash>>>verify)&&&konst (scriptHash (recipient dest))>>>eq>>>verify)
          &&&((konst (w32 i)>>>primitive Prim.OutputValue>>>verify)&&&konst (w64 amount)>>>eq>>>verify)>>>unit
  guard (Same i)=(konst (w32 i)>>>primitive Prim.OutputScriptHash>>>verify)&&&(unit>>>Tx.currentScriptHash)>>>eq>>>verify
  guard (Remain i maxSpend)=((((unit>>>Tx.currentValue)&&&konst (w64 maxSpend))>>>A.subtract word64)>>> (oh>>>not iden>>>verify)&&&ih>>>ih)
                    &&&(konst (w32 i)>>>primitive Prim.OutputValue>>>verify)>>>A.le word64>>>verify
  guard (Oracle outcome)=checkSigWith (pk 4) (konst (w256FromBytes (attMsg outcome))) (sigAt 4>>>verify)

sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
spend lock sq outs=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 (BL.fromStrict ourScript) sq] [mkOutput (fromInteger v) s|(v,s)<-outs] lock) 0 defaultTap
zeroW=(0,w256 0,replicate 5 Nothing)
entry (App ident title spec assumptions branches scenarios)=Entry ("app-"++ident) title spec BitcoinApp
 (Derived "BIP340 signatures from Ref.Bip340; independently constructed boundary transactions; negative transactions re-signed to isolate each covenant or timelock")
 ("Complete bounded spend condition only; off-chain setup, liveness, and foreign-chain verification remain protocol responsibilities":assumptions)
 (\w->Prog (program branches w)) [Vector name env (mkW mode is secret env) ex|Scenario name mode lock sq outs is secret ex<-scenarios,let env=spend lock sq outs]
 where
  mkW mode is secret env=(mode,w256FromBytes secret,[if i `elem` is then Just (sigW (signMsg (keys!!i) (msg i))) else Nothing|i<-[0..4]])
   where
    ordinary=case env (progCmr (Prog (program branches zeroW))) >>= (\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of Just m->w256ToBytes m; _->error "app message"
    msg i=if ident=="dlc-enumerated" && i==4 then attMsg mode else ordinary

normal=[(99000,recipient 0)]
s name mode lock sq is ex=Scenario name mode lock sq normal is preimage ex
tx name mode lock sq outs is ex=Scenario name mode lock sq outs is preimage ex
bolt="BOLT #3 transaction output scripts https://github.com/lightning/bolts/blob/master/03-transactions.md"
babylon="Babylon Bitcoin staking scripts https://github.com/babylonlabs-io/btc-staking-ts"
entries :: [Entry]
entries=map entry
 [App "lightning-to-local" "Lightning delayed to_local output with revocation" bolt ["Schnorr adaptation; revocation immediately or owner after CSV144"]
   [(0,[Signed 0]),(1,[Signed 1,Relative 144])]
   [s "revocation" 0 0 0xffffffff [0] Accept,s "owner after CSV" 1 0 144 [1] Accept,s "owner one block early" 1 0 143 [1] Reject,s "wrong owner" 1 0 144 [0] Reject]
 ,App "lightning-anchor" "Lightning anchor owner/anyone spend" bolt ["owner immediately or anyone after CSV16"]
   [(0,[Signed 0]),(1,[Relative 16])]
   [s "owner immediately" 0 0 0xffffffff [0] Accept,s "anyone after sixteen" 1 0 16 [] Accept,s "anyone early" 1 0 15 [] Reject,s "wrong owner" 0 0 0xffffffff [1] Reject]
 ,App "lightning-received-htlc" "Lightning received HTLC: revocation, success and timeout" bolt ["bounded Schnorr adaptation; preimage actually hashed; sender/receiver both sign success"]
   [(0,[Signed 2]),(1,[Hashlock,Signed 0,Signed 1]),(2,[Absolute 850000,Signed 1])]
   [s "revocation" 0 0 0xffffffff [2] Accept,s "hashlock plus both signatures" 1 0 0xffffffff [0,1] Accept,s "missing signature" 1 0 0xffffffff [0] Reject,s "timeout" 2 850000 0xfffffffe [1] Accept,s "timeout early" 2 849999 0xfffffffe [1] Reject,Scenario "wrong preimage" 1 0 0xffffffff normal [0,1] (BS.replicate 32 0) Reject]
 ,App "inheritance" "Inheritance owner path and delayed heir quorum" "Liana recovery wallet https://wizardsardine.com/liana/" ["owner or2-of-3 heirs after absolute height900000"]
   [(0,[Signed 0]),(1,[Absolute 900000,Threshold 2 [1,2,3]])]
   [s "owner" 0 0 0xffffffff [0] Accept,s "heirs quorum" 1 900000 0xfffffffe [1,3] Accept,s "heirs early" 1 899999 0xfffffffe [1,3] Reject,s "one heir" 1 900000 0xfffffffe [1] Reject]
 ,App "decaying-multisig" "Decaying multisig with two timed threshold transitions" "Miniscript thresh/after/or policies https://bitcoin.sipa.be/miniscript/" ["three signatures now, two after height900000, one after950000; one program includes all thresholds"]
   [(0,[Threshold 3 [0,1,2]]),(1,[Absolute 900000,Threshold 2 [0,1,2]]),(2,[Absolute 950000,Threshold 1 [0,1,2]])]
   [s "all now" 0 0 0xffffffff [0,1,2] Accept,s "two at first decay" 1 900000 0xfffffffe [0,2] Accept,s "one at second decay" 2 950000 0xfffffffe [1] Accept,s "second decay early" 2 949999 0xfffffffe [1] Reject,s "insufficient initial quorum" 0 0 0xffffffff [0,1] Reject]
 ,App "statechain-recovery" "Statechain owner/server transfer and delayed recovery" "Statechains https://github.com/RubenSomsen/rubensomsen.github.io/blob/master/statechains.pdf" ["server co-signs transfers; owner recovery after CSV1008; off-chain transfer protocol is outside this leaf"]
   [(0,[Signed 0,Signed 3]),(1,[Signed 0,Relative 1008])]
   [s "owner plus server" 0 0 0xffffffff [0,3] Accept,s "owner recovery" 1 0 1008 [0] Accept,s "server cannot steal" 0 0 0xffffffff [3] Reject,s "recovery early" 1 0 1007 [0] Reject]
 ,App "ark-unilateral-exit" "Ark bounded unilateral VTXO exit" "Ark VTXO exit https://docs.ark-protocol.org/" ["fixed exit payout and anchor template; CSV144; VTXO tree construction is outside this leaf"]
   [(0,[Signed 0,Relative 144,Count 2,Pay 0 0 99000,Pay 1 1 330])]
   [tx "exit" 0 0 144 [(99000,recipient 0),(330,recipient 1)] [0] Accept,tx "early exit" 0 0 143 [(99000,recipient 0),(330,recipient 1)] [0] Reject,tx "payout diverted" 0 0 144 [(99000,recipient 2),(330,recipient 1)] [0] Reject,tx "underpaid exit" 0 0 144 [(98999,recipient 0),(330,recipient 1)] [0] Reject]
 ,App "ark-forfeit" "Ark VTXO forfeit pays the operator" "Ark forfeit transaction https://docs.ark-protocol.org/" ["owner and operator authorize one fixed payout; connectors and presigning are off chain"]
   [(0,[Signed 0,Signed 3,Count 1,Pay 0 3 99000])]
   [tx "joint forfeit" 0 0 0xffffffff [(99000,recipient 3)] [0,3] Accept,tx "operator alone" 0 0 0xffffffff [(99000,recipient 3)] [3] Reject,tx "wrong beneficiary" 0 0 0xffffffff [(99000,recipient 0)] [0,3] Reject]
 ,App "coinpool-close" "CoinPool three-party cooperative close with fixed allocation" "CoinPool https://coinpool.dev/coinpool.pdf" ["all three members consent to a fixed three-output allocation; pool updates remain off chain"]
   [(0,[Threshold 3 [0,1,2],Count 3,Pay 0 0 40000,Pay 1 1 30000,Pay 2 2 29000])]
   [tx "agreed allocation" 0 0 0xffffffff allocation [0,1,2] Accept,tx "missing member" 0 0 0xffffffff allocation [0,1] Reject,tx "allocation altered" 0 0 0xffffffff [(40001,recipient 0),(29999,recipient 1),(29000,recipient 2)] [0,1,2] Reject]
 ,App "dlc-enumerated" "Enumerated DLC oracle-attested payout covenant" "DLC oracle events https://github.com/discreetlogcontracts/dlcspecs" ["fixed event ID with two outcomes; direct oracle check replaces pre-signed adaptor setup"]
   [(0,[Oracle 0,Count 2,Pay 0 0 70000,Pay 1 1 29000]),(1,[Oracle 1,Count 2,Pay 0 0 20000,Pay 1 1 79000])]
   [tx "first outcome" 0 0 0xffffffff [(70000,recipient 0),(29000,recipient 1)] [4] Accept,tx "second outcome" 1 0 0xffffffff [(20000,recipient 0),(79000,recipient 1)] [4] Accept,tx "oracle payout altered" 0 0 0xffffffff [(69999,recipient 0),(29001,recipient 1)] [4] Reject,tx "no oracle" 0 0 0xffffffff [(70000,recipient 0),(29000,recipient 1)] [] Reject]
 ,App "arbitrated-escrow" "Two-party escrow with arbitrated fixed refunds" "Miniscript escrow plus covenant https://bitcoin.sipa.be/miniscript/" ["cooperative close or arbitrator+one participant; arb cannot redirect refund"]
   [(0,[Signed 0,Signed 1]),(1,[Signed 0,Signed 2,Pay 0 0 99000,Count 1]),(2,[Signed 1,Signed 2,Pay 0 1 99000,Count 1])]
   [s "cooperative close" 0 0 0xffffffff [0,1] Accept,tx "buyer refund" 1 0 0xffffffff [(99000,recipient 0)] [0,2] Accept,tx "seller refund" 2 0 0xffffffff [(99000,recipient 1)] [1,2] Accept,tx "arbitrator alone" 1 0 0xffffffff [(99000,recipient 0)] [2] Reject,tx "refund diverted" 1 0 0xffffffff [(99000,recipient 2)] [0,2] Reject]
 ,App "fidelity-bond" "JoinMarket-style timelocked fidelity bond redemption" "JoinMarket fidelity bonds https://github.com/JoinMarket-Org/joinmarket-clientserver/blob/master/docs/fidelity-bonds.md" ["timestamp CLTV at1800000000; Schnorr adaptation of the published timelocked owner script"]
   [(0,[Signed 0,AbsoluteTime 1800000000])]
   [s "mature bond" 0 1800000000 0xfffffffe [0] Accept,s "immature bond" 0 1799999999 0xfffffffe [0] Reject,s "wrong owner" 0 1800000000 0xfffffffe [1] Reject]
 ,App "reserve-preserving-spend" "Reserve custody rollover preserves asset value" "BIP127 proof-of-reserves ownership motivation https://github.com/bitcoin/bips/blob/master/bip-0127.mediawiki" ["fee<=1000; all remaining reserve continues under same script; not a zero-knowledge liability proof"]
   [(0,[Signed 0,Same 0,Remain 0 1000,Count 1])]
   [tx "reserve rolls with fee" 0 0 0xffffffff [(99000,ourScript)] [0] Accept,tx "reserve depleted" 0 0 0xffffffff [(98999,ourScript)] [0] Reject,tx "reserve script altered" 0 0 0xffffffff [(99000,recipient 0)] [0] Reject]
 ,App "babylon-unbonding" "Babylon-style staking unbonding and delayed withdrawal" babylon ["staker plus2-of-3 committee unbonds; staker alone after CSV1008; separate witness roles"]
   [(0,[Signed 0,Threshold 2 [2,3,4],Count 1,Pay 0 0 99000]),(1,[Signed 0,Relative 1008])]
   [tx "committee unbond" 0 0 0xffffffff [(99000,recipient 0)] [0,2,4] Accept,s "delayed withdrawal" 1 0 1008 [0] Accept,tx "one committee member" 0 0 0xffffffff [(99000,recipient 0)] [0,2] Reject,s "early withdrawal" 1 0 1007 [0] Reject]
 ,App "babylon-slashing" "Babylon-style staking slashing payout" babylon ["staker, finality provider and2-of-3 committee authorize fixed slash/return; secret extraction remains off chain"]
   [(0,[Signed 0,Signed 1,Threshold 2 [2,3,4],Count 2,Pay 0 4 10000,Pay 1 0 89000])]
   [tx "slash distribution" 0 0 0xffffffff [(10000,recipient 4),(89000,recipient 0)] [0,1,2,3] Accept,tx "missing finality provider" 0 0 0xffffffff [(10000,recipient 4),(89000,recipient 0)] [0,2,3] Reject,tx "slash amount altered" 0 0 0xffffffff [(9999,recipient 4),(89001,recipient 0)] [0,1,2,3] Reject]
 ,App "recurring-payment" "Recurring UTXO payment with preserved principal" "Safe AllowanceModule periodic-payment semantics https://github.com/safe-global/safe-modules" ["payer signs; recipient gets10000; principal retains script with fee<=1000; each spend restarts CSV144"]
   [(0,[Signed 0,Relative 144,Count 2,Pay 0 1 10000,Same 1,Remain 1 11000])]
   [tx "scheduled payment" 0 0 144 [(10000,recipient 1),(89000,ourScript)] [0] Accept,tx "early payment" 0 0 143 [(10000,recipient 1),(89000,ourScript)] [0] Reject,tx "principal drained" 0 0 144 [(10000,recipient 1),(88999,ourScript)] [0] Reject,tx "wrong recipient" 0 0 144 [(10000,recipient 2),(89000,ourScript)] [0] Reject]
 ]
 where allocation=[(40000,recipient 0),(30000,recipient 1),(29000,recipient 2)]
