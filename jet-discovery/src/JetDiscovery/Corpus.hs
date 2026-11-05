-- | The full corpus, in GOAL.md priority order.
-- Run from the jet-discovery directory: some entries read vectors from vendor-specs/.
module JetDiscovery.Corpus
  ( corpus
  ) where

import qualified JetDiscovery.Corpus.FibonacciStark as FibonacciStark
import qualified JetDiscovery.Corpus.ContractExpansion as ContractExpansion
import qualified JetDiscovery.Corpus.EprintExpansion as EprintExpansion
import qualified JetDiscovery.Corpus.FairSwap as FairSwap
import qualified JetDiscovery.Corpus.BN254 as BN254
import qualified JetDiscovery.Corpus.ScriptProposals as ScriptProposals
import qualified JetDiscovery.Corpus.BitcoinExpansion as BitcoinExpansion
import qualified JetDiscovery.Corpus.BitcoinGrowth as BitcoinGrowth
import qualified JetDiscovery.Corpus.BitcoinGrowth2 as BitcoinGrowth2
import qualified JetDiscovery.Corpus.BitcoinClients as BitcoinClients
import qualified JetDiscovery.Corpus.TransportCrypto as TransportCrypto
import qualified JetDiscovery.Corpus.WebAuthn as WebAuthn
import qualified JetDiscovery.Corpus.Poseidon2 as Poseidon2
import qualified JetDiscovery.Corpus.Blake3 as Blake3
import qualified JetDiscovery.Corpus.Shake256 as Shake256
import qualified JetDiscovery.Corpus.ContractGrowth as ContractGrowth
import qualified JetDiscovery.Corpus.CumulativeSplitter as CumulativeSplitter
import qualified JetDiscovery.Corpus.SablierStream as SablierStream
import qualified JetDiscovery.Corpus.UmaBond as UmaBond
import qualified JetDiscovery.Corpus.QuadraticFunding as QuadraticFunding
import qualified JetDiscovery.Corpus.SnapshotGovernor as SnapshotGovernor
import qualified JetDiscovery.Corpus.UniswapV2Pool as UniswapV2Pool
import qualified JetDiscovery.Corpus.NexusMutual as NexusMutual
import qualified JetDiscovery.Corpus.Clipper as Clipper
import qualified JetDiscovery.Corpus.ContractMessageApps as ContractMessageApps
import qualified JetDiscovery.Corpus.ContractBridge as ContractBridge
import qualified JetDiscovery.Corpus.ClaimProtocols as ClaimProtocols
import qualified JetDiscovery.Corpus.NativeLoan as NativeLoan
import qualified JetDiscovery.Corpus.NativeOcr as NativeOcr
import qualified JetDiscovery.Corpus.NativeBatchOrders as NativeBatchOrders
import qualified JetDiscovery.Corpus.StablePool as StablePool
import qualified JetDiscovery.Corpus.WeightedPool as WeightedPool
import qualified JetDiscovery.Corpus.NativePmmPool as NativePmmPool
import qualified JetDiscovery.Corpus.NativeLmsrMarket as NativeLmsrMarket
import qualified JetDiscovery.Corpus.NativePendleMarket as NativePendleMarket
import qualified JetDiscovery.Corpus.NativeV3Pool as NativeV3Pool
import qualified JetDiscovery.Corpus.MlDsaNtt as MlDsaNtt
import qualified JetDiscovery.Lib.HdWallet as HdWallet
import qualified JetDiscovery.Corpus.Xmss as Xmss
import qualified JetDiscovery.Corpus.Bip360P2mr as Bip360P2mr
import qualified JetDiscovery.Corpus.ContractMath as ContractMath
import qualified JetDiscovery.Corpus.Lms as Lms
import qualified JetDiscovery.Corpus.FinancialApps as FinancialApps
import qualified JetDiscovery.Corpus.StatefulApps as StatefulApps
import qualified JetDiscovery.Corpus.ProposalApps as ProposalApps
import qualified JetDiscovery.Corpus.StateMachines as StateMachines
import JetDiscovery.Types (Entry)
import qualified JetDiscovery.Corpus.Baseline as Baseline
import qualified JetDiscovery.Corpus.Bip348Csfs as Csfs
import qualified JetDiscovery.Corpus.Bip119Ctv as Ctv
import qualified JetDiscovery.Corpus.Bip446TemplateHash as TemplateHash
import qualified JetDiscovery.Corpus.CovenantMisc as CovenantMisc
import qualified JetDiscovery.Corpus.Apps as Apps
import qualified JetDiscovery.Corpus.Shrincs as Shrincs
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark
import qualified JetDiscovery.Corpus.DeFi as DeFi
import qualified JetDiscovery.Corpus.MoreBips as MoreBips
import qualified JetDiscovery.Corpus.Ripemd as Ripemd
import qualified JetDiscovery.Corpus.Aggregate as Aggregate
import qualified JetDiscovery.Corpus.Bip346Txhash as Txhash
import qualified JetDiscovery.Corpus.ShrincsStateless as ShrincsStateless
import qualified JetDiscovery.Corpus.SlhDsaStandard as SlhDsaStandard
import qualified JetDiscovery.Corpus.StarkFri as StarkFri
import qualified JetDiscovery.Corpus.P256 as P256
import qualified JetDiscovery.Corpus.Ed25519 as Ed25519
import qualified JetDiscovery.Corpus.Eprint as Eprint
import qualified JetDiscovery.Corpus.EthSol as EthSol

corpus :: IO [Entry]
corpus = concat <$> sequence
  [ pure Baseline.entries
  , Csfs.entries
  , Ctv.entries
  , TemplateHash.entries
  , Txhash.entries
  , pure CovenantMisc.entries
  , MoreBips.entries
  , pure Apps.entries
  , pure Ripemd.entries
  , pure Aggregate.entries
  , pure Shrincs.entries
  , pure ShrincsStateless.entries
  , pure SlhDsaStandard.entries
  , pure Hashes.entries
  , pure P256.entries
  , pure Ed25519.entries
  , pure Stark.entries
  , pure StateMachines.entries
  , pure ProposalApps.entries
  , pure StatefulApps.entries
  , pure Lms.entries
  , pure FinancialApps.entries
  , pure ContractMath.entries
  , Bip360P2mr.entries
  , pure Xmss.entries
  , pure BitcoinExpansion.entries
  , BitcoinGrowth.entries
  , BitcoinGrowth2.entries
  , BitcoinClients.entries
  , fmap (:[]) HdWallet.entry
  , TransportCrypto.entries
  , pure WebAuthn.entries
  , pure Poseidon2.entries
  , Blake3.entries
  , Shake256.entries
  , pure MlDsaNtt.entries
  , pure ScriptProposals.entries
  , pure FibonacciStark.entries
  , pure ContractExpansion.entries
  , pure ContractGrowth.entries
  , pure CumulativeSplitter.entries
  , pure [SablierStream.entry]
  , pure [UmaBond.entry]
  , pure QuadraticFunding.entries
  , pure [SnapshotGovernor.entry]
  , pure UniswapV2Pool.entries
  , pure [NexusMutual.entry]
  , pure [Clipper.entry]
  , pure ContractMessageApps.entries
  , pure ContractBridge.entries
  , pure ClaimProtocols.entries
  , pure NativeLoan.entries
  , pure NativeOcr.entries
  , pure NativeBatchOrders.entries
  , pure StablePool.entries
  , pure WeightedPool.entries
  , pure NativePmmPool.entries
  , pure NativeLmsrMarket.entries
  , pure NativePendleMarket.entries
  , pure NativeV3Pool.entries
  , pure EprintExpansion.entries
  , pure FairSwap.entries
  , pure BN254.entries
  , pure DeFi.entries
  , Eprint.entries
  , pure EthSol.entries
  ]
