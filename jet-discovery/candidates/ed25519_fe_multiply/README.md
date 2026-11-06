# Candidate: `ed25519_fe_multiply` — multiplication modulo 2^255 - 19

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: Large savings in one interoperability verifier still leave a substantial residual. Benchmark raw field reduction and compare the dedicated curve and SHA-512 pieces before pursuing this as a broadly demanded jet.

Price: **0.813 WU (ESTIMATE)**. FeMultiply: 2^255-19 reduction is as cheap as secp256k1's (fold by 38)

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 5,835 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-ed25519 | native_full_verifier | 5835 | 1 | 2,925,636.828 | 566,826.408 | 2,358,810.420 | no / no at 18820 WU |

See the [complete matrix](../../reports/candidate-ranking.md#ed25519_fe_multiply) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

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

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
