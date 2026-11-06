# Candidate: `signature_unpack` — BIP 340 signature parsing

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: A small field/scalar range proof is attractive, but direct measured demand is concentrated in variable-message CSFS. Compare shared range checks and full Schnorr verification before selecting the frontend.

Price: **1.156 WU (ESTIMATE)**. FeNormalize + ScalarNormalize: range checks on r and s

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 1 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bip348-csfs | native_full_verifier | 1 | 1 | 408.282 | 194.580 | 213.702 | yes / yes at 775 WU |

See the [complete matrix](../../reports/candidate-ranking.md#signature_unpack) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Word256, Word256) -> S (Word256, Word256)`

## Specification
The exact Simplicity expression is `Simplicity.Programs.LibSecp256k1.Lib.signature_unpack`. Return `Right (r,s)` with both words unchanged when r is below the secp256k1 field prime p and s is below the scalar order n. Return `Left ()` otherwise. This arrow accepts zero components in range and performs no signature equation. The Integer specification and direct arrow test are in [Tests.hs](../../test/Tests.hs), with p and n from [Ref.Bip340](../../src/JetDiscovery/Ref/Bip340.hs).

## Cost (ESTIMATE)
ESTIMATE: `FeNormalize` + `ScalarNormalize` = 1.156 WU.

## Generality
As for `pubkey_unpack_neg`.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. A C implementation compares the two raw 256-bit words with p and n, writes the exact choice tag, and copies both unmodified words on success. At the read-only `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd`, `Coq/C/JET_ACCEPTANCE.md` lists `fe_normalize` and `scalar_normalize` as existing verified integrations. Their fixed-width field/scalar representation and exact output/frame relations inform the proof. The new proof must establish both raw range comparisons and the joint sum/product encoding. The pinned acceptance document gives the local Clight proof scope and separates focused tip evidence from earlier whole-project acceptance.

## Alternatives considered
See `pubkey_unpack_neg`.
