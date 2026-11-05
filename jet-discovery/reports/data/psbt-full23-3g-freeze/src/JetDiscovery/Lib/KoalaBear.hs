-- | Exact total word semantics of the fixed-prime addition frontend used by
-- the complete KoalaBear16 Poseidon2 program. No new consensus jet.
module JetDiscovery.Lib.KoalaBear (addRef,q) where
import Prelude hiding(drop,take)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Arith as A
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes(konst,w32)

q :: Integer
q=2130706433

-- | u=(a+b) mod2^32; return u if u<q, otherwise u-q.
-- Canonical operands produce field addition, since2q<2^32. For other input
-- words this deliberately retains wrap/single-subtraction behavior; it is
-- neither arbitrary-word modular addition nor a rejecting range-check jet.
addRef :: Assert t => t(Word32,Word32)Word32
addRef=A.add word32>>>ih>>>canon
 where
  canon=((iden&&&konst(w32 q))>>>A.subtract word32)&&&iden>>>
    ((ooh&&&(ih&&&oih))>>>cond oh ih)
