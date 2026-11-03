# Candidate: `sha512_compress` — SHA-512 compression function

## Type signature
`(Vector8 Word64, Vector16 Word64) -> Vector8 Word64`

## Specification
`JetDiscovery.Corpus.Ed25519.sha512Compress` (FIPS 180-4); reproduces the FIPS 180-4 digest of "abc" and the
SHA-512 values inside the RFC 8032 ed25519 test vectors.

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `Sha256Block` = 1.147 WU (80 rounds on 64-bit words over a 128-byte block, as `blake2b_compress`).

## Generality
Ed25519 (RFC 8032) challenge hashes, BIP 32 / SLIP-10 HMAC-SHA512 key derivation, Solana and Cardano signatures.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: the SHA-256 compression proof structure carries over with 64-bit words.

## Alternatives considered
None smaller: the whole ed25519 verification jet would include it.

## Corpus evidence
- `xchain-sha512`: matched ×1 (static multiplicity); program cost 5454.166 WU → 17.797 WU with all candidates (306.5×).
- `xchain-ed25519`: matched ×1 (the challenge hash).

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
