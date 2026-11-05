-- | Independent byte-oriented reference encodings for the bounded applications.
-- These are local test/reference routines, never a downloaded implementation.
module JetDiscovery.Ref.BitcoinGrowth
 ( bip322MessageHash,bip322ToSpend,bip322ToSign,bip322DigestFromHash,bip322Digest
 , sha256d,le32,le64,p2trScript
 ) where
import qualified Data.ByteString as B
import Data.Serialize (runPut,putWord32le,putWord64le)
import JetDiscovery.Tx (sha256,hashToBytes,taggedSha256,unhex)

le32 n=runPut(putWord32le(fromInteger n))
le64 n=runPut(putWord64le(fromInteger n))
sha b=hashToBytes(sha256 b)
sha256d=sha.sha
p2trScript key=unhex "5120"<>key
bip322MessageHash message=hashToBytes(taggedSha256 "BIP0322-signed-message" message)

-- One null input with OP_0 PUSH32 message_hash; one zero-valued P2TR output.
bip322ToSpend messageHash key
 | B.length messageHash/=32||B.length key/=32=error "BIP322 requires 32-byte hashes/keys"
 | otherwise=le32 0<>B.singleton 1<>B.replicate 32 0<>le32 0xffffffff
    <>unhex "220020"<>messageHash<>le32 0<>B.singleton 1<>le64 0
    <>B.singleton 34<>p2trScript key<>le32 0

-- Canonical non-witness serialization. The simple proof supplies one 64-byte
-- keypath witness signature; the legacy txid excludes that witness as usual.
bip322ToSign messageHash key=le32 0<>B.singleton 1<>sha256d(bip322ToSpend messageHash key)
 <>le32 0<>B.singleton 0<>le32 0<>B.singleton 1<>le64 0<>unhex "016a"<>le32 0

-- BIP341 SIGHASH_DEFAULT, keypath/no annex, nVersion=0, nLockTime=0,
-- one zero-valued input, sequence=0, and exactly one zero-valued OP_RETURN.
bip322DigestFromHash messageHash key=hashToBytes(taggedSha256 "TapSighash" sigmsg)
 where
  outpoint=sha256d(bip322ToSpend messageHash key)<>le32 0
  script=p2trScript key
  sigmsg=unhex "0000"<>le32 0<>le32 0
   <>sha outpoint<>sha(le64 0)<>sha(B.singleton 34<>script)<>sha(le32 0)
   <>sha(le64 0<>unhex "016a")<>B.singleton 0<>le32 0
bip322Digest message key=bip322DigestFromHash(bip322MessageHash message)key
