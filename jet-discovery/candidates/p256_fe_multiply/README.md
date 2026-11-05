# Candidate: `p256_fe_multiply` — multiplication in the P-256 base field

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

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
- `p256_ecdsa_verify` (curve-level): far cheaper per verification and a single proof obligation, at a higher burden.
- Generic `multiply_256` + `div_mod_512`: general, but leaves the reduction plumbing in Simplicity.

## Corpus evidence
- `xchain-p256-ecdsa` (RFC 6979 A.2.5 vectors): matched ×7686 (static multiplicity); program cost 8860683.872 WU → 702329.516 WU with all candidates (12.6×), still 17.6% of `BUDGET_MAX`.
- Mining: the Solinas reduction (`W512 -> W256`, 1,061 WU per instance, ×7686) is the top sub-DAG of the whole corpus (68.5% of the corpus bound).
- Conclusion: a field jet alone does not make P-256 usable; see `p256_ecdsa_verify`.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
