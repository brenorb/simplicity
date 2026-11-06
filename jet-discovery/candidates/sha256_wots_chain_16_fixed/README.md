# Candidate: `sha256_wots_chain_16_fixed`

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Strong**: Prioritize the fixed-prefix frontend: both stateless variants cross their fixed-stack scenarios and share one counting group. The separate stateful group uses the generic frontend; its overlay prices the observed 18-byte buffer, and the unrestricted 30-compression path needs a separate price.

Price: **11.475 WU (ESTIMATE)**. ESTIMATE: 15 x Sha256Block for the fixed 18-byte-address n16 chain frontend; same primitive family as sha256_wots_chain_16

Matches in 2 of 157 registered rows: 2 matched DAG nodes across all branches, 420 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| pq-shrincs-stateless | native_full_verifier | 175 | 1 | 198,670.811 | 20,607.261 | 178,063.550 | no / yes at 23664 WU |
| pq-slh-dsa-sha2-128s | native_full_verifier | 245 | 1 | 275,877.127 | 26,588.157 | 249,288.970 | no / yes at 29787 WU |

See the [complete matrix](../../reports/candidate-ranking.md#sha256_wots_chain_16_fixed) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

This is the fixed-width frontend of the SHA-256 WOTS chain primitive family.
It makes the expensive verification step executable without carrying a
variable-length SHA context through every chain. It is a candidate overlay
only; it does not register a consensus jet.

## Type and exact specification

```haskell
type AddressPrefix = ((Word8,Word64),(Word8,(Word32,Word32)))
type ChainInput = (Word256,(AddressPrefix,(Word4,Word128)))
chainRef :: Assert term => term ChainInput Word128
```

The first word is a SHA-256 compression midstate. The prefix encodes
`layer1 || tree8 || type1 || keypair4 || chain4`, big endian, exactly 18 bytes.
For `j=start..14`, compute

```text
node = first16(SHA256Compress(state,
         prefix18 || j_be32 || node16 || 0x80 || zero17 || 816_be64))
```

Every iteration uses the same supplied midstate. `start=15` returns the node
without hashing. The final length is 816 bits because the caller has already
compressed a 64-byte block and the suffix has 38 bytes. The helper `seedState`
compresses `publicSeed16 || zero48` under the standard SHA-256 IV. Address
consistency and public-key/message binding are responsibilities of the caller;
this pure kernel contains no witness nodes or authorization policy.

The Simplicity reference is
[`Lib.ShrincsHash.chainRef`](../../src/JetDiscovery/Lib/ShrincsHash.hs).
The separate Haskell byte/compression specification is
[`Ref.ShrincsHash.chainSpec`](../../src/JetDiscovery/Ref/ShrincsHash.hs), using
`Digest.compress`/`freeStart` over the independent Haskell SHA backend.
`seedStateSpec`, `encodePrefix` and 18 `seededCases` support normal tests,
including an actual stateful type-16 address and stateless type-0 addresses.
The full protocol source is the pinned
[SHRINCS draft](../../vendor-specs/shrincs/SHRINCS.md), whose revision and
license are recorded in its [manifest](../../vendor-specs/MANIFEST.md).

## Corpus evidence and counting

`pq-shrincs-stateless` supplies the bound public seed/address, digest-derived
start and a chain node that enters once. Its five layers have 35 chains each:
**175 source-level calls**, each with at most 15 hash steps. This is an expected
structural multiplicity; actual matcher occurrences, WU, what-if savings and
budget feasibility must be taken from the fresh runner/mining artifacts.
Historical costs for the unbound verifier do not apply to the repaired rows.
The full repaired verifier's seven standalone vectors pass. The complete
run reports its cost and candidate impact separately.

The standard `pq-slh-dsa-sha2-128s` baseline uses the same kernel in seven
35-chain layers, or **245 source-level calls**. It belongs to the same hash-family
parameter counting group as the SHRINCS stateless row. All seven native-message
vectors and the four-vector official NIST fixture pass; these source call counts
still require actual candidate matching and cost analysis.

`pq-shrincs-stateful` retains the generic `Ctx8` frontend
`Lib.Kernels.wotsChain`, which already has a distinct candidate expression.
Both frontends represent one primitive family in recommendation/group counting;
they must not inflate either the application count or claimed generality.
This fixed form accepts type 16 as well as type 0, but current stateful corpus
matching must not be attributed to it without changing and remeasuring that
program.

## Cost estimate and proof burden

The overlay uses **11.475 WU ESTIMATE**, or `15 * cost("Sha256Block")` at the
unchanged in-tree benchmark price. The fixed layout needs exactly one
compression per executed iteration and up to 15 iterations. The seeded first
block remains in the caller. The price approximates compression work. A C
benchmark must also cover the loop, block assembly, and result truncation.

The generic context frontend currently uses the same price for its measured
18-byte caller alignment. Its typed input permits alignments that need two
compressions per iteration. The fixed frontend is the simpler benchmark
target for this address layout. [Generic frontend and price scope](../sha256_wots_chain_16/README.md)

The implementation burden is moderate by analogy with the existing proven
SHA-256 compression primitive: a bounded loop, exact 18+4+16-byte packing,
fixed padding, truncation and the start-15 identity case. A C prototype should
reuse the existing compression implementation and use fixed buffers. The new
proof work composes at most 15 compression steps, establishes the prefix and
padding byte order, and proves the branch/loop invariant. This is a qualitative
estimate; no Coq proof or C benchmark is supplied here.

The read-only proof analogue inspected on `feat/jet-equivalence`, revision
`771d41b98acc3750308a07c76405125bbc8439cd`, is
`Coq/C/jet_sha_block_literal.v`, especially
`literal_sha_256_block_matches`; its saved assumptions snapshot records this
semantic equality as closed. That file explicitly leaves canonical source
correspondence and public/startup composition as separate obligations. It is
evidence for reuse of the compression specification, not a completed proof of
this new C loop or a claim that every C linkage obligation is discharged.

The generic context frontend accepts a wider set of prefixes. A one-step F
kernel keeps the 15 conditional steps in Simplicity, and a full
signature-verifier jet adds scheme-specific work. The fixed chain form supports
both pinned SHRINCS address domains and the SLH-DSA-SHA2-128s layout. The current
stateful row retains its generic expression and matches that frontend. RFC8391
XMSS randomized masks and RFC8554 LMS n32 chains require their own exact
relations.

## Validation

`tools/StatelessWotsProbe.hs` checks the expression against independent
`Ref.Shrincs.tweak` byte hashing, including starts 0/7/15, chain 0/34 and both
address domains. The completed 36-case run is recorded in
[`shrincs-direct-wots-kernel.txt`](../../reports/data/shrincs-direct-wots-kernel.txt)
with a separate actual exit-status JSON. The full updated stateless verifier
passed all seven vectors (actual exit0,1145.480 seconds, maximum heap residency
15273293304 bytes under a16GiB cap), recorded in its
`shrincs-stateless-direct-witness-bound` log/status. Earlier heap-exhausted
constructions remain separate diagnostics and are not passes.
