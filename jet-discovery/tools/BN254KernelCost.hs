-- | Typed arithmetic-arrow costs, without entry witness/canonical/equality
-- wrappers. Complements the complete native corpus-vector measurements.
module Main where
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.MerkleRoot(CommitmentRoot,commitmentRoot)
import Simplicity.Ty.Word
import Simplicity.Weight(milliWeight)
import Simplicity.Bitcoin.Benchmarks(cost)
import JetDiscovery.Cost(TermWeight,milliWeigh)
import qualified JetDiscovery.Corpus.BN254 as B
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
fp :: J.WrappedSimplicity(Word256,Word256)Word256
fp=J.jetSubst B.fpMul
fp2 :: J.WrappedSimplicity((Word256,Word256),(Word256,Word256))(Word256,Word256)
fp2=J.jetSubst B.fp2Mul
main=do
 hSetBuffering stdout LineBuffering
 putStrLn("fp_kernel_cmr="++show(commitmentRoot(J.unwrap fp :: CommitmentRoot(Word256,Word256)Word256)))
 putStrLn("fp_kernel_native_mwu="++show(milliWeigh(J.unwrap fp :: TermWeight(Word256,Word256)Word256)))
 putStrLn("fp2_kernel_cmr="++show(commitmentRoot(J.unwrap fp2 :: CommitmentRoot((Word256,Word256),(Word256,Word256))(Word256,Word256))))
 putStrLn("fp2_kernel_native_mwu="++show(milliWeigh(J.unwrap fp2 :: TermWeight((Word256,Word256),(Word256,Word256))(Word256,Word256))))
 putStrLn("fp_jet_price_mwu_estimate="++show(milliWeight(2*cost "FeMultiply")))
