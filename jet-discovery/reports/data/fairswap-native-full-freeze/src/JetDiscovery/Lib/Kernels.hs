-- | Reusable kernels shared by corpus programs and by candidate-jet
-- specifications ("JetDiscovery.Candidates.Registry").  Keeping them here
-- (with no witness nodes and no dependency on the runner) lets the what-if
-- overlay match them by identity Merkle root wherever programs use them.
module JetDiscovery.Lib.Kernels
  ( sha256Pair
  , wotsStep, wotsChain
  , nibble8
  ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes (konst, w8, w32)

-- | SHA-256 of a 64-byte concatenation (a Merkle node; OP_CAT + OP_SHA256 in Script).
sha256Pair :: Assert term => term Word512 Word256
sha256Pair = (unit >>> ctx8Init) &&& iden >>> ctx8Add64 >>> ctx8Finalize

nibble8 :: Core term => term Word4 Word8
nibble8 = konst (toWord4 0) &&& iden

-- | One step of a SHA-256 tweaked Winternitz chain (SHRINCS WOTS+C / FIPS 205 WOTS):
-- input (context holding the address up to the chain index, (start index, node)).
-- If start <= j then node := F(address || j, node), truncated to 16 bytes.
wotsStep :: Assert term => Int -> term (Ctx8, (Word4, Word128)) (Ctx8, (Word4, Word128))
wotsStep j = oh &&& (ioh &&& (((ioh >>> nibble8) &&& konst (w8 (toInteger j)) >>> Arith.le word8) &&& iden >>> cond f iih))
 where f = (oh &&& konst (w32 (toInteger j)) >>> ctx8Add4) &&& iih >>> ctx8Add16 >>> ctx8Finalize >>> oh

-- | A full chain from its start index to 15 (w = 16): 15 conditional steps.
wotsChain :: Assert term => term (Ctx8, (Word4, Word128)) Word128
wotsChain = foldr (\j k -> wotsStep j >>> k) iden [0 .. 14] >>> iih
