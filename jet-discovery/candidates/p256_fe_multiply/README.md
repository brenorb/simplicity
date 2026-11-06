# Candidate: `p256_fe_multiply` — multiplication in the P-256 base field

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: Dedicated reduction saves 9,233,450.936 WU in each of the two P-256-based predicates. Residual estimates of 826,747.503 WU for standalone verification and 829,907.725 WU for WebAuthn still exceed their 13,272- and 19,725-WU fixed-stack scenarios. Benchmark the field ABI and compare a reusable curve-level verifier.

Price: **1.219 WU (ESTIMATE)**. 1.5 x FeMultiply: a P-256 field multiply with Solinas reduction is somewhat slower than libsecp256k1's

Matches in 2 of 157 registered rows: 2 matched DAG nodes across all branches, 17,422 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-p256-ecdsa | native_full_verifier | 8711 | 1 | 10,060,198.439 | 826,747.503 | 9,233,450.936 | no / no at 13272 WU |
| app-webauthn-counter-wallet | native_full_spend | 8711 | 1 | 10,063,358.661 | 829,907.725 | 9,233,450.936 | no / no at 19725 WU |

See the [complete matrix](../../reports/candidate-ranking.md#p256_fe_multiply) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

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
