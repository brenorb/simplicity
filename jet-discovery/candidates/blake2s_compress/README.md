# Candidate: `blake2s_compress` — BLAKE2s compression function

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Rejected**: The exact fixed final-block frontend only matches its own kernel and shares one counting group with BLAKE2b. Broader rounds or common G helpers need a distinct exact reference and new evidence.

Price: **0.765 WU (ESTIMATE)**. Sha256Block: BLAKE2s compression and SHA-256 compression cost about the same in software

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 1 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| xchain-blake2s-compress | kernel | 1 | 1 | 3,256.768 | 4.330 | 3,252.438 | no / yes at 1976 WU |

See the [complete matrix](../../reports/candidate-ranking.md#blake2s_compress) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`((Vector8 Word32, Vector16 Word32), (Word32, Word32)) -> Vector8 Word32` (final-block flag set)

## Specification
`JetDiscovery.Corpus.Hashes.blake2F blake2s`; passes the RFC 7693 Appendix B vector.

## Cost (ESTIMATE)
ESTIMATE: `Sha256Block` = 0.765 WU (similar work per 64-byte block).

## Generality
BLAKE2s, and BLAKE3 (same G function, 7 rounds, different flags); STARK commitment hashes (Stwo uses BLAKE2s).

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. The structure is close to the proven SHA-256 compression: 32-bit add/xor/rotate rounds.

## Alternatives considered
A BLAKE3-specific compression jet would serve BLAKE3 directly. The final-block flag should become an input.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
