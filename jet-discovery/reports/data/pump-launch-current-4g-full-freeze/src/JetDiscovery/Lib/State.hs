-- | Native Bitcoin state commitment in an unknown-log Taproot internal key.
-- State is32 bytes; every continuation retains the same executable leaf.
-- This adapts simplicity-contracts' TapData commitment scheme to available
-- Bitcoin terms without introducing any consensus primitive.
module JetDiscovery.Lib.State (loadState,stateScriptHash,stateScript,stateTap) where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString as BS
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.Bitcoin.Lib as B
import Simplicity.Bitcoin.Term (Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.DataTypes as D
import Simplicity.LibSecp256k1.Schnorr (PubKey(..))
import Simplicity.Ty.Word
import JetDiscovery.Corpus.CovenantMisc (embedDataT)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R

loadState :: (Assert t,Primitive t,TyC a) => t a Word256 -> t a ()
loadState old=(((konst (w256 R.nums)&&&old)>>>embedDataT)&&&(unit>>>primitive P.InternalKey)>>>eq>>>verify)
 &&&((konst (w8 0)>>>primitive P.Tappath>>>isSome>>>not iden)>>>verify)>>>unit
stateScriptHash :: (Assert t,Primitive t,TyC a) => t a Word256 -> t a Word256
stateScriptHash new=(((unit>>>ctx8Init)&&&konst (w16 0x5120)>>>ctx8Add2)&&&key)>>>ctx8Add32>>>ctx8Finalize
 where key=((((konst (w256 R.nums)&&&new)>>>embedDataT)&&&(unit>>>SH.tapleafHash))>>>B.buildTaptweak)
stateTap :: Hash256 -> BS.ByteString -> D.TapEnv
stateTap cmr dat=(defaultTap cmr){D.tapInternalKey=PubKey (fromInteger (R.embedData R.nums dat))}
stateScript :: Hash256 -> BS.ByteString -> BS.ByteString
stateScript cmr dat=unhex "5120"<>R.bytesFromInt (R.taprootTweak (R.embedData R.nums dat) (hashToBytes (D.tapleafHash (defaultTap cmr))))
