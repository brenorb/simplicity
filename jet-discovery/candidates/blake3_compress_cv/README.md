# Candidate: `blake3_compress_cv`

<!-- final-corpus-evidence:start -->

## Final corpus evidence

Full-run fingerprint: `5e8dc436ec69e679a073380ad0a4dd440d46bb8792fffaf4bf0c89d45b6329f0`.

**Maybe**: The bounded BitVM-style tree-hash component has substantial savings but remains one use family. Benchmark the raw CV/first-output-block ABI and compare it with smaller round helpers before proposing a jet.

Price: **0.535 WU (ESTIMATE)**. ESTIMATE: 7/10 of the BLAKE2s compression analogue (Sha256Block), scaled by 7 vs 10 rounds; no BLAKE3 C benchmark

Matches in 1 of 157 registered rows: 1 matched DAG nodes across all branches, 33 selected-path occurrences before family deduplication.

| program | scope | selected occurrences | matched DAG nodes | native WU | isolated WU ESTIMATE | saved WU ESTIMATE | fixed hypothetical fit before / after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| crypto-blake3-tree-hash | kernel | 33 | 1 | 139,215.660 | 10,154.805 | 129,060.855 | no / no at 6756 WU |

See the [complete matrix](../../reports/candidate-ranking.md#blake3_compress_cv) for zero-match rows and competing scenarios. The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, measured C price, or consensus feasibility claim.

<!-- final-corpus-evidence:end -->

The prototype is a local cost overlay. Its type is
`(Vector8 Word32,(Vector16 Word32,(Word64,(Word32,Word32)))) -> Vector8 Word32`.
Inputs are the eight chaining words, sixteen block words, the 64-bit counter,
and the 32-bit block length and flags. Run the seven BLAKE3 rounds and return
the first eight feed-forward words, `v[i] XOR v[i+8]` for `i=0..7`. The function
is total on raw words, including out-of-range lengths and reserved flag bits.
The enclosing hash chooses its legal length and flags. Output is in word
order; byte serialization is outside this arrow.

- Simplicity: `JetDiscovery.Corpus.Blake3.compressChainingSpec`, an `Assert`
  expression matching the native chunk, parent and 256-bit root helper.
  Haskell: the first eight words of `JetDiscovery.Ref.Blake3.compress`, an
  independent `Word32`/list implementation of the pinned
  [BLAKE3 specification](../../vendor-specs/crypto-families/blake3-spec.pdf).
- The normal reference test checks empty block, chunk, high counter, parent,
  and raw length/flags boundary cases. A separate [equivalence run](../../reports/data/blake3-cv-api-equivalence-verification.txt)
  checked eight controls on each of the original, current native and pure
  expressions. Their native jetted CMR, static bound (3,911.570 WU), program
  length (13,010 bits) and absence of witnesses were identical. These are
  arrow measurements, before any overlay.
- Price: **ESTIMATE**, 0.7 × the benchmark-derived `Sha256Block` price. This
  scales the existing BLAKE2s cost analogue by seven versus ten rounds; both
  mix 32-bit words. A real C benchmark may differ with setup, feed-forward
  and CPU acceleration. The current registry rounds this analogue to **0.535 WU (ESTIMATE)**.
- Demand: this expression is used by the bounded unkeyed BLAKE3-256 hash, with a Bitcoin dispute path evidenced by the pinned
  [BitVM BLAKE3 source](../../vendor-specs/crypto-families/bitvm-blake3.rs.txt).
  The complete corpus run records matches, per-program isolated savings
  and budget effects. All 22 standalone native hash vectors pass, including
  all 19 supported official cases; see [validation](../../reports/CRYPTO-FAMILIES.md).
  This candidate adds no corpus group.
- Burden: medium. C needs 16 local state words, fixed add/XOR/rotate operations,
  seven message schedules and eight feed-forward outputs. At the read-only
  `feat/jet-equivalence` revision `771d41b98acc3750308a07c76405125bbc8439cd`,
  `Coq/C/jet_add32_wide_word.v` and `Coq/C/jet_right_rotate_wide_word.v`
  provide word-level proof patterns. A new proof must establish the state
  layout, round and schedule, and exact total output for raw flags and length.
  Their [read-only hashes](../../reports/data/blake3-cv-proof-analogues.json)
  pin the evidence. They do not prove the new arrow.
- Alternatives: compose the existing word jets; add just the common BLAKE
  `G` mixing step to share more code across BLAKE variants at a smaller match
  size; or expose all 16 output words to support longer XOF output at a
  different interface and proof cost. The eight-word prototype targets the
  actual chunk and 256-bit root call sites. It does not implement streaming,
  tree dispatch, keyed mode or arbitrary-length XOF.
