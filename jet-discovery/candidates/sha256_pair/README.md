# Candidate: `sha256_pair` — SHA-256 of a 64-byte concatenation

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: A simple Merkle helper has several direct matches and a reusable proof path. Compare its smaller savings and the full verifier residual with existing two-compression composition before adding a separate fixed-size jet.

Price: **1.530 WU (ESTIMATE)**. 2 x Sha256Block: SHA-256 of 64 bytes is two compressions

Matches in 7 of 157 registered rows: 7 matched DAG nodes across all branches, 7,202 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| app-merkle-key | native_full_spend | 16 | 1 | 242.966 | 176.886 | 66.080 | yes / yes at 940 WU |
| app-payment-pool-merkle-exit | native_full_spend | 4 | 1 | 442.566 | 426.046 | 16.520 | yes / yes at 804 WU |
| app-payment-pool-funded-deposit | native_full_spend | 4 | 1 | 372.067 | 355.547 | 16.520 | yes / yes at 725 WU |
| app-payment-pool-internal-transfer | native_full_spend | 8 | 1 | 522.699 | 489.659 | 33.040 | yes / yes at 968 WU |
| app-merkle-distributor-bitmap | native_full_spend | 2 | 1 | 408.583 | 400.323 | 8.260 | yes / yes at 1076 WU |
| app-bitcoin-spv-payment-receipt | native_full_spend | 1 | 1 | 1,294.901 | 1,290.771 | 4.130 | yes / yes at 3614 WU |
| stark-fibonacci-full | native_full_verifier | 7167 | 1 | 1,497,462.342 | 1,467,862.632 | 29,599.710 | no / no at 286745 WU |

See the [complete matrix](../../reports/candidate-ranking.md#sha256_pair) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`Word512 -> Word256`

## Specification
`JetDiscovery.Lib.Kernels.sha256Pair`: one Merkle-node hash (OP_CAT + OP_SHA256 in Script).

## Cost (ESTIMATE)
ESTIMATE: 2 x `Sha256Block` = 1.530 WU.

## Generality
Merkle paths (tree signatures, STARK commitments, BitVM, any SHA-256 Merkle tree).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Low. It is a composition of proven jets (`sha256_ctx_8_init`, `add_64`, `finalize`); the proof is mostly gluing existing lemmas.

## Alternatives considered
Today it is three jets plus plumbing; a "hash two 32-byte nodes" jet with a tag or sort option would also serve BIP 341 TapBranch-style trees.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
