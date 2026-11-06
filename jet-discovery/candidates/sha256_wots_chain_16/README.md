# Candidate: `sha256_wots_chain_16` — SHA-256 tweaked Winternitz chain (w = 16, n = 16)

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: Prioritize the fixed-prefix frontend: both stateless variants cross their fixed-stack scenarios and share one counting group. The separate stateful group uses the generic frontend; its overlay prices the observed 18-byte buffer, and the unrestricted 30-compression path needs a separate price.

Price: **11.475 WU (ESTIMATE)**. 15 x Sha256Block for the matched 18-byte buffer alignment; a caller-profile ESTIMATE. An unrestricted valid context can require 30 compressions.

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 32 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| pq-shrincs-stateful | native_full_verifier | 32 | 1 | 15,175.556 | 8,335.428 | 6,840.128 | no / no at 3933 WU |

See the [complete matrix](../../reports/candidate-ranking.md#sha256_wots_chain_16) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

## Type signature
`(Ctx8, (Word4, Word128)) -> Word128`

## Specification
The arrow uses the supplied `Ctx8` as the same prefix at each iteration. For `j` from the start index through 14, append the four-byte big-endian index and 16-byte node, finalize SHA-256, and use the first 16 digest bytes as the next node. Context operations reject invalid contexts or lengths on a hash step. Start 15 returns the node directly, so that branch never examines the context. [Simplicity expression](../../src/JetDiscovery/Lib/Kernels.hs)

The stateful SHRINCS caller supplies the prefix `pk_seed16 || zero48 || ADRS[0:18]`, which leaves exactly 18 buffered bytes after the first compression.

## Cost (ESTIMATE)
The current overlay uses 15 × `Sha256Block`, or **11.475 WU ESTIMATE**. This prices the measured stateful caller profile with 18 buffered prefix bytes. Appending 20 bytes leaves 38 buffered bytes, so each iteration takes one compression for finalization.

The typed context allows up to 63 buffered bytes. At 36 through 43 bytes, appending 20 leaves 56 through 63 bytes and finalization takes two compressions. At 44 through 63 bytes, the append itself compresses one block and finalization compresses another. A valid context in either range can therefore require 30 compressions over 15 iterations. A full-context worst-path compression analogue would be **22.950 WU ESTIMATE**, with context handling and control flow still to benchmark. The saved overlays use the 11.475 WU caller-profile price. The fixed frontend has a single compression at every supported step. [Fixed frontend](../sha256_wots_chain_16_fixed/README.md)

## Generality
This frontend serves SHA-256 chains with `w = 16`, a 16-byte node, and the same four-byte-index suffix. The stateful SHRINCS verifier uses it for 32 source-level chain calls. The current stateless SHRINCS and SLH-DSA-SHA2-128s rows use the fixed frontend. These are two interfaces in one primitive family. Schemes with different address layouts, masks, node lengths, or hash functions require separate equivalence evidence. In particular, RFC8391 XMSS and RFC8554 LMS have different hash relations.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. The SHA block and context lemmas provide proof patterns. The generic arrow adds a bounded loop, buffer and length handling for an arbitrary supplied context, and the start-15 identity branch. The verifier using the arrow supplies the proper scheme-specific address prefix.

## Alternatives considered
A single tweakable hash with the fixed prefix would fuse one compression step and leave the 15 conditional steps in Simplicity. A monolithic `shrincs_verify` would cover the scheme-specific verifier. The chain can also remain composed from the existing SHA-256 context jets.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
