# koalabear_add

Prototype overlay only; no consensus registration, encoding or native C jet.

- Type: `(Word32,Word32) -> Word32`.
- Exact total specification: let `u=(a+b) mod2^32`; return `u` when
  `u<2130706433`, otherwise return `u-2130706433`. Canonical field operands
  produce their field sum because `2q<2^32`. Every other32-bit input also has
  defined behavior. This is a wrap-add/single-subtract helper, not general
  modular addition and not a range-rejecting field API. In particular,
  maximum-word inputs return2164260861, which exceeds q.
- Simplicity expression: `JetDiscovery.Lib.KoalaBear.addRef`, exactly matching
  the existing Poseidon2 frontend without changing that program. Independent
  Integer reference: `JetDiscovery.Ref.KoalaBear.addWordSpec`.
- Test:281 raw-word pairs, including q/2q/carry boundaries and200 generated
  pairs, against the independent Integer model; explicit noncanonical-output
  regression. The normal candidate-reference test group runs it.
- Price: **ESTIMATE**, the sum of the in-tree `Add32` and `Subtract32`
  benchmark-derived prices. This is an analogue, not a measured new C
  implementation. The generated candidate-price table is authoritative.
- Demand: the complete KoalaBear16 Poseidon2 component, including both the
  published Plonky3 and exact Bitcoin-verifier constant profiles. Their
  shared field/frontend is one family. Source/provenance is in
  [CRYPTO-FAMILIES.md](../../reports/CRYPTO-FAMILIES.md). The existing native
  profile identified the repeated3.667WU addition frontend as a hotspot.
- Generality/burden: a fixed field-specific frontend has less generality than
  an arbitrary-modulus primitive. C is an unsigned add, subtraction and
  selection; Coq can reuse the32-bit addition/borrow patterns. The new proof
  must establish wrap and single-subtraction semantics for every input word,
  then separately establish the canonical-field corollary. No proof is
  supplied or implied. Read-only proof analogies use the same
  `feat/jet-equivalence` evidence revision documented in
  [METHOD.md](../../reports/METHOD.md).
- Alternatives: compose existing Add32/Subtract32 and case selection as now;
  a generic add-modulus primitive would have a different type/specification;
  a monolithic Poseidon2 jet would require substantially more new proof and
  a concrete choice of parameters. A total mathematical modulo operation
  cannot replace this exact expression on noncanonical words.

Tier remains **maybe**: the current demand signal is one component family.
Budget effects remain conditional on the first-vector hypothetical scenario,
with no candidate encoding or deployment claim. The final complete matrix
must retain all zero matches, isolated alternatives and per-program savings.

## Completed pre-final isolated measurement

All14 actual Poseidon2 vectors and every analysis field complete successfully
with the new overlay. The original program, native cost and CMR are unchanged.
The281-pair independent-reference test passes separately. Exact run, source,
snapshot and price provenance is in
[koalabear-add-impact-pre-final.json](../../reports/data/koalabear-add-impact-pre-final.json).

| program | native WU | exact occurrences | jet price WU ESTIMATE | isolated WU ESTIMATE | saved WU ESTIMATE |
| --- | ---: | ---: | ---: | ---: | ---: |
| crypto-poseidon2-koalabear16 |10,947.177 |1884 |0.179 |4,564.185 |6,382.992 |

The first vector serializes to51,775program bits and1,025witness bits.
This is component evidence, not a complete native application or a fresh
whole-corpus ranking. The full run still must establish whether any other
program contains this exact expression. The proof analogies are pinned in
[koalabear-proof-analogues.json](../../reports/data/koalabear-proof-analogues.json):
`jet_add32_wide_word.v`, `jet_add32_layout_exec.v`,
`jet_subtract_spec.v` and `jet_full_subtract_word.v` at revision
`771d41b98acc3750308a07c76405125bbc8439cd`. They inform the burden judgement;
they do not prove this new candidate.
