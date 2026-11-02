# Candidate: `sha256_wots_chain_16` — SHA-256 tweaked Winternitz chain (w = 16, n = 16)

## Type signature
`(Ctx8, (Word4, Word128)) -> Word128`

## Specification
`JetDiscovery.Lib.Kernels.wotsChain`: from a SHA-256 context holding `pk_seed || zeros(48) || ADRS[0:18]`, iterate `node := SHA-256(ctx || j || node)[0:16]` for j from the start index to 14. This is SHRINCS's WOTS+C chain and FIPS 205 (SLH-DSA-SHA2) WOTS chain iteration for n = 16.

## Cost (ESTIMATE)
ESTIMATE: 15 x `Sha256Block` (0.383 WU each) = 5.739 WU, the worst case (a jet has a fixed cost). The existing ctx jets show context reads and writes are cheap next to compression.

## Generality
Primitive for the whole SHA-256 hash-based signature family: SHRINCS (both paths), SLH-DSA-SHA2 (FIPS 205), XMSS and LMS-style chains, and BitVM-style Winternitz bit commitments. Parameters: w = 16, n = 16; a 32-byte-node variant would cover n = 32 schemes.

## Verification burden (judgement, by analogy with jets proven on `feat/jet-equivalence`)
Medium. It composes the already proven SHA-256 compression with a data-dependent iteration count (at most 15). The SHA block and ctx lemmas from the totals branch apply directly; the new part is the bounded loop and the address encoding.

## Alternatives considered
(a) A single tweakable-hash jet (one F call, 1 compression): it removes the context-threading cost but keeps 15 conditional steps per chain in the static bound. (b) A monolithic `shrincs_verify` jet: the largest saving, but tied to one draft scheme. (c) Keeping chains in Simplicity: about 225 WU per chain in the static bound.

## Corpus evidence
- `pq-shrincs-stateful`: matched ×32 (static multiplicity); program cost 8039.435 WU → 1199.307 WU with all candidates (6.7×).
- Mining: the chain sub-DAG (225.3 WU per instance, x32) is the top shape in reports/subdags.md, 21.3% of the whole corpus bound and 89.7% of `pq-shrincs-stateful`. The single F step (12.3 WU, x448 in the bound) is next.

Test: `cabal test` checks this specification against an independent Haskell reference (test/Tests.hs).
