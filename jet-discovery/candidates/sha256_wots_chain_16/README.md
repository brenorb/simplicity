# Candidate: `sha256_wots_chain_16` — SHA-256 tweaked Winternitz chain (w = 16, n = 16)

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`(Ctx8, (Word4, Word128)) -> Word128`

## Specification
The arrow uses the supplied `Ctx8` as the same prefix at each iteration. For `j` from the start index through 14, append the four-byte big-endian index and 16-byte node, finalize SHA-256, and use the first 16 digest bytes as the next node. Context operations reject invalid contexts or lengths on a hash step. Start 15 returns the node directly, so that branch never examines the context. [Simplicity expression](../../src/JetDiscovery/Lib/Kernels.hs)

The stateful SHRINCS caller supplies the prefix `pk_seed16 || zero48 || ADRS[0:18]`, which leaves exactly 18 buffered bytes after the first compression.

## Cost (ESTIMATE)
The current overlay uses 15 × `Sha256Block`, or **11.475 WU ESTIMATE**. This prices the measured stateful caller profile with 18 buffered prefix bytes. Appending 20 bytes leaves 38 buffered bytes, so each iteration takes one compression for finalization.

The typed context allows up to 63 buffered bytes. At 36 through 43 bytes, appending 20 leaves 56 through 63 bytes and finalization takes two compressions. At 44 through 63 bytes, the append itself compresses one block and finalization compresses another. A valid context in either range can therefore require 30 compressions over 15 iterations. A full-context worst-path compression analogue would be **22.950 WU ESTIMATE**, with context handling and control flow still to benchmark. The saved overlays use the 11.475 WU caller-profile price. The fixed frontend has a single compression at every supported step. [Fixed frontend](../sha256_wots_chain_16_fixed/README.md)

## Generality
This frontend serves SHA-256 chains with `w = 16`, a 16-byte node, and the same four-byte-index suffix. The current stateful SHRINCS row uses it directly. The current stateless SHRINCS and SLH-DSA-SHA2-128s rows use the fixed frontend. These are two interfaces in one primitive family. Schemes with different address layouts, masks, node lengths, or hash functions require separate equivalence evidence. In particular, RFC8391 XMSS and RFC8554 LMS have different hash relations.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. The SHA block and context lemmas provide proof patterns. The generic arrow adds a bounded loop, buffer and length handling for an arbitrary supplied context, and the start-15 identity branch. The verifier using the arrow supplies the proper scheme-specific address prefix.

## Alternatives considered
(a) A single tweakable-hash jet (one F call, 1 compression): it removes the context-threading cost but keeps 15 conditional steps per chain in the static bound. (b) A monolithic `shrincs_verify` jet: the largest saving, but tied to one draft scheme. (c) Keeping chains in Simplicity: about 225 WU per chain in the static bound.

## Corpus evidence
- `pq-shrincs-stateful`: matched ×32 (static multiplicity); program cost 8039.435 WU → 1199.307 WU with all candidates (6.7×).
- `pq-shrincs-stateless` (SLH-DSA path): matched ×175; program cost 58344.501 WU → 20937.551 WU (2.8×).
- Mining: the chain sub-DAG (225.3 WU per instance, x32) was the top shape of the first 25-program corpus (21.3% of its bound) and is 89.7% of `pq-shrincs-stateful`; the 49-program corpus's bound is dominated by the P-256 field reductions. The single F step (12.3 WU, x448 in the bound) is next.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
