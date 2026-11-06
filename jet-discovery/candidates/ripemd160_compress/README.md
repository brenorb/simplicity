# Candidate: `ripemd160_compress` — RIPEMD-160 compression function

## Type signature
`((Word32, Word32, Word32, Word32, Word32), Vector16 Word32) -> (Word32, Word32, Word32, Word32, Word32)`
(state and message words little-endian, as in the RIPEMD-160 specification)

## Specification
`JetDiscovery.Lib.Ripemd160.ripemd160Compress`; reproduces the published RIPEMD-160 digests of "" and "abc"
(`xchain-ripemd160`, `cabal test`).

## Cost (ESTIMATE)
ESTIMATE: `Sha256Block` = 0.765 WU (RIPEMD-160's 160 steps on 32-bit words cost about one SHA-256 compression in
software).

## Generality
Bitcoin-native: HASH160 (`RIPEMD160(SHA256(x))`) is Script's key hash (P2PKH, P2WPKH) and the BOLT 3 HTLC payment
hash. Script-compatible HTLCs, PTLC fallbacks and key-hash commitments need it. Also Ethereum's ripemd160
precompile.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium, like SHA-256 compression: a fixed sequence of 32-bit operations with two parallel lines. The C code is in
Bitcoin Core (`crypto/ripemd160.cpp`), not libsecp256k1.

## Alternatives considered
A whole `hash160_32` jet (SHA-256 then RIPEMD-160 of a 32-byte value) covers the HTLC and key-hash uses in one call.

## Reference checks

The standalone probe matches all ten direct compressor calls against `JetDiscovery.Corpus.Ripemd.ripemd160Ref`. It starts from the standard IV and passes one padded block for each message, including the empty message and the 55-byte single-block limit. [Probe](../../tools/HashCompressionReferenceProbe.hs) · [Results](../../reports/data/hash-compression-reference-probe.txt) · [Provenance](../../reports/data/hash-compression-reference-provenance.json)
