-- | Test/setup helpers for correctly committing a native Simplicity leaf.
-- Only public Bitcoin library operations are used; no consensus code is changed.
module JetDiscovery.Lib.BitcoinFunding(fundingScript,fundingSecret) where
import qualified Data.ByteString as B
import Simplicity.Bitcoin.DataTypes(TapEnv(..),tapleafHash,taptweak)
import Simplicity.LibSecp256k1.Schnorr(PubKey(..))
import JetDiscovery.Tx(unhex,hashToBytes)
import qualified JetDiscovery.Ref.Bip340 as R

fundingScript tap
 | not(null(tappath tap))=error "fundingScript supports a single leaf/no siblings"
 | otherwise=case taptweak(tapInternalKey tap)(tapleafHash tap)of
    Just(PubKey x)->unhex "5120"<>R.bytesFromInt(toInteger x)
    _->error "invalid Taproot funding key"

-- Test-only private setup computation. The result is never a witness. The
-- resulting public output is checked against the Bitcoin library's taptweak.
fundingSecret secret tap
 | secret<=0||secret>=R.n=Nothing
 | not(null(tappath tap))=Nothing
 | R.pubkeyOf secret/=toInteger internal=Nothing
 | tweak>=R.n=Nothing
 | output==0=Nothing
 | fundingScript tap/=unhex "5120"<>R.bytesFromInt(R.pubkeyOf output)=Nothing
 | otherwise=Just output
 where
  PubKey internal=tapInternalKey tap
  Just point=R.pointMul R.gPt secret
  normalized=if R.hasEvenY point then secret else R.n-secret
  tweak=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt(toInteger internal)<>hashToBytes(tapleafHash tap)))
  output=(normalized+tweak)`mod`R.n
