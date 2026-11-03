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

## Corpus evidence
- `xchain-ripemd160`: matched ×1 (static multiplicity); program cost 2469.559 WU → 14.139 WU with all candidates (174.7×).
- `app-htlc-hash160` (BOLT 3-style HTLC with a HASH160 payment hash): 2546.490 WU → 91.070 WU (28.0×). The SHA-256 HTLC `app-htlc` costs 62.340 WU.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
