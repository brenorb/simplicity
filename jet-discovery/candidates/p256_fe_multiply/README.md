# Candidate: `p256_fe_multiply` — multiplication in the P-256 base field

## Type signature
`(Word256, Word256) -> Word256` (inputs and output reduced mod p = 2^256 - 2^224 + 2^192 + 2^96 - 1)

## Specification
`JetDiscovery.Corpus.P256.mulmod`: `multiply word256`, then a Solinas reduction (FIPS 186-5 D.1.2.3 style).

## Cost (ESTIMATE)
ESTIMATE: 1.5 x `FeMultiply` = 1.219 WU (a P-256 multiply with Solinas reduction is somewhat slower than
libsecp256k1's secp256k1 field multiply).

## Generality
P-256 / secp256r1 only: passkeys and WebAuthn, secure elements and HSMs, X.509, Ethereum's P256VERIFY (RIP-7212 /
EIP-7951).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium to high: a new prime, so the u128-oracle `fe_multiply` proof is a template, not a reuse. The C code would be
new (not libsecp256k1).

## Alternatives considered
- A curve-level `p256_ecdsa_verify` could fuse the full verification equation and would require a broader proof.
- Generic `multiply_256` + `div_mod_512`: general, but leaves the reduction plumbing in Simplicity.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
