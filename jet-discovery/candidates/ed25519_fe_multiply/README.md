# Candidate: `ed25519_fe_multiply` — multiplication modulo 2^255 - 19

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Word256, Word256) -> Word256` (inputs and output reduced mod 2^255 - 19)

## Specification
`JetDiscovery.Corpus.Ed25519.mulmod`: `multiply word256`, then two folds by 38 and a canonical reduction.

## Cost (ESTIMATE)
ESTIMATE: `FeMultiply` = 0.813 WU (2^255 - 19 reduces as cheaply as secp256k1's prime).

## Generality
Ed25519 (RFC 8032; Solana, Cardano, Tor, SSH, Signal keys) and X25519.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium: a pseudo-Mersenne prime close to secp256k1's case; the `fe_multiply` u128 oracles are a direct template.

## Alternatives considered
- An `ed25519_verify` jet (curve-level, with `sha512_compress` inside).
- Generic `multiply_256` + `div_mod_512`.

## Corpus evidence
- `xchain-ed25519` (RFC 8032 TEST 1-3): matched ×5835 (static multiplicity); program cost 2925312.642 WU → 557349.793 WU with all candidates (5.2×), still 13.9% of `BUDGET_MAX`.
- Conclusion: as for P-256, a curve-level `ed25519_verify` jet would be needed for ed25519 to be practical.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
