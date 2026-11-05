-- | Baseline programs: ordinary key spends.  They calibrate the measurements
-- (a single BIP 340 signature check over the default sighash costs about 50 WU).
module JetDiscovery.Corpus.Baseline
  ( entries
  , sigAllMessage
  , signMsg
  , signSigAll
  , toSig
  ) where

import qualified Data.ByteString as BS
import Data.Word (Word32)

import Simplicity.Digest (Hash256)
import Simplicity.LibSecp256k1.Schnorr (PubKey(..), Sig(..))
import Simplicity.Programs.CheckSig.Lib (checkSigVerify', sigHash')
import Simplicity.Bitcoin.DataTypes (SigTx)
import Simplicity.Bitcoin.Primitive (PrimEnv)
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Ty.Word (fromWord256)

import JetDiscovery.Types
import JetDiscovery.Tx
import JetDiscovery.Run (progCmr)
import qualified JetDiscovery.Ref.Bip340 as Ref

-- | The message signed by 'checkSigVerify'' with the jetted 'SigHash.sigAllHash' mode.
sigAllMessage :: PrimEnv -> Maybe BS.ByteString
sigAllMessage env = Ref.bytesFromInt . fromWord256 <$> Jets.fastEval (sigHash' (unwrap (Jets.jetSubst SigHash.sigAllHash))) env ()

toSig :: BS.ByteString -> Sig
toSig s = Sig (fromInteger (Ref.intFromBytes (BS.take 32 s))) (fromInteger (Ref.intFromBytes (BS.drop 32 s)))

-- | Sign an arbitrary message with BIP 340.
signMsg :: Integer -> BS.ByteString -> Sig
signMsg sk msg = toSig (Ref.sign sk msg (BS.replicate 32 0))

signSigAll :: Integer -> PrimEnv -> Sig
signSigAll sk env = maybe (error "signSigAll: sighash evaluation failed") (signMsg sk) (sigAllMessage env)

p2pk :: PubKey -> Sig -> Prog
p2pk pk sig = Prog (checkSigVerify' (unwrap (Jets.jetSubst SigHash.sigAllHash)) pk sig)

sk1 :: Integer
sk1 = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF

pk1 :: PubKey
pk1 = PubKey (fromInteger (Ref.pubkeyOf sk1))

spendTx :: Word32 -> SigTx
spendTx lock = mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffd] [mkOutput 99000 (unhex "5120" <> BS.replicate 32 7)] lock

envFor :: Word32 -> Hash256 -> Maybe PrimEnv
envFor lock = mkEnv (spendTx lock) 0 defaultTap

-- The CMR does not depend on the witness, so any signature gives the real CMR.
cmr :: Hash256
cmr = progCmr (p2pk pk1 (Sig 0 0))

sigFor :: Word32 -> Sig
sigFor lock = maybe (error "env") (signSigAll sk1) (envFor lock cmr)

entries :: [Entry]
entries =
  [ Entry
    { entryId = "baseline-p2pk-sigall"
    , entryTitle = "Single BIP 340 key spend over sig_all_hash"
    , entrySpec = "Simplicity.Programs.CheckSig.checkSigVerify' with Simplicity.Bitcoin.Programs.SigHash.sigAllHash"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "signature over the jetted sig_all_hash message, made with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["one input, one output"]
    , entryProgram = p2pk pk1
    , entryVectors =
        [ Vector "valid signature" (envFor 0) (sigFor 0) Accept
        , Vector "signature made for a different locktime" (envFor 0) (sigFor 1) Reject
        ]
    }
  ]
