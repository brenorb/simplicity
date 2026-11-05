-- | Transparent sharing of the existing local ECDSA specifications, at their
-- minimal closed operand types. No new jet or price is introduced.
module JetDiscovery.Lib.Ecrecover where
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import qualified JetDiscovery.Corpus.ContractExpansion as C

type Recovery=(Word256,(Word256,(Word256,Bit)))
type Verification=(((Word256,Word256),Word256),(Word256,Word256))
recoverWrapped :: J.WrappedSimplicity Recovery Word256
recoverWrapped=J.jetSubst C.ecRecover
{-# NOINLINE recoverWrapped #-}
verifyWrapped :: J.WrappedSimplicity Verification ()
verifyWrapped=J.jetSubst C.ecdsaVerify
{-# NOINLINE verifyWrapped #-}
recoverShared :: Simplicity t => t Recovery Word256
recoverShared=J.unwrap recoverWrapped
verifyShared :: Simplicity t => t Verification ()
verifyShared=J.unwrap verifyWrapped
