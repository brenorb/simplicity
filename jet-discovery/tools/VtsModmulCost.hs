-- | Static cost of one modular multiplication at RSA sizes, for the
-- verifiable-timed-signature ESTIMATE in reports/FOLLOW-UP.md.
--
-- a * b mod N = (multiply word_k (a, b)) div_mod (0, N), the same exact
-- Integer-style reduction as JetDiscovery.Corpus.BN254.fpMul, on existing
-- Bitcoin jets (jet substitution lowers the products to 64-bit multiply jets).
-- Cost via the corpus cost algebra on the jet-substituted DAG.
module Main where
import Prelude hiding (drop, take)
import System.Environment (getArgs)
import Simplicity.Term.Core
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Ty.Word
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Cost (TermWeight, milliWeigh)

main :: IO ()
main = do
  [k] <- getArgs
  case k of
    "1024" -> print (milliWeigh (J.unwrap (J.jetSubst m1024) :: TermWeight (Word1024, (Word1024, Word1024)) Word1024))
    "2048" -> print (milliWeigh (J.unwrap (J.jetSubst m2048) :: TermWeight (Word2048, (Word2048, Word2048)) Word2048))
    _ -> error "1024 | 2048"
 where
  -- input (N, (a, b))
  m1024 = (drop (Arith.multiply word1024) &&& ((unit >>> Arith.zero word1024) &&& oh)) >>> Arith.div_mod word2048 >>> ih >>> ih
  m2048 = (drop (Arith.multiply word2048) &&& ((unit >>> Arith.zero word2048) &&& oh)) >>> Arith.div_mod word4096 >>> ih >>> ih
