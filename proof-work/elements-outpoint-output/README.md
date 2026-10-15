# Three getter contracts and shared indexed-result conversion

Kernel-checked, unregistered endpoints:
`simplicity_input_prev_outpoint`, `simplicity_current_prev_outpoint`, and
`simplicity_output_script_hash`. Each new theorem preserves the entire original
`application_jet_local_spec_sep` contract and its original six-assumption set.
No admission, new axiom, unchecked cast, or new libc premise is used.

The new `C.jet_elements_indexed_literal` module has eight results and five
definitions. Two helpers are closed:

- `elements_indexed_literal_matches`, polymorphic over environment, element,
  and Simplicity payload type, lifts a pointwise payload encoding equality
  through the actual indexed lookup and canonical input-word decoder.
- `haskell_encode_outpoint_matches` composes the checked four-limb digest
  conversion with the checked low-bit-first word conversion for the index.

The current getter reuses `elements_current_literal_sem`; no current-index
assertion or arbitrary-width bit proof is duplicated. When applying the new
indexed helper, supply its payload type explicitly: Coq cannot infer `B` from
`tySem B` for a pair, because that interpretation is not injective. The checked
outpoint proof uses `@elements_indexed_literal_matches Elements.env sigTxInput
(Ty.Prod Word256 Word32) ...`.

## Evidence and reproducible checkpoint review

Private tree: `/private/tmp/jet-elements-outpoint-output.q4tx08d7`.
Fingerprint:
`f5724eb56b628fb01fb7b9ccc5fe24bc868a3feb7adfcfeddfb6d90177bc4f50`.
All 1,584 inherited sources/metadata/registries match the completed immutable
annex tree. The checker verifies all 24 inherited module objects against that
tree's receipt; it does **not** claim they were freshly compiled in this run.
Only the new module and the assumption/type report drivers are freshly
compiled. Full reports cover all eight result types and five definitions,
without ellipses/evars. Recursive checking includes both original execution
roots and the new module, with the unchanged kernel context.

`CHECKED.json` binds the base, preserved main inputs/index, source/object hashes,
exact commands, successful terminal statuses, reports, and driver. The later
independent evidence review rejects promotion of this checkpoint to canonical
review/coverage, incomplete inventories and modified source/log evidence.

```sh
python3 -B proof-work/elements-outpoint-output/review.py
python3 -B proof-work/elements-outpoint-output/test-review.py
```

## Supplementary canonical-source review

The earlier `CHECKED.json` and `EVIDENCE-REVIEW.json` deliberately retain their
historical `canonical_source_review_complete: false` status. The subsequent
`PREPARATION.json` and `SOURCE-REVIEW.json` establish the selected source review
without rewriting that history. Normal registration/full acceptance remain
**false**, coverage added remains zero, and no proof is installed in main.

The supplementary guard checks:

1. The three exact catalog identities/types/bindings, Haskell `atInput` and
   `atOutput`, `encodeOutpoint`'s hash/index pair order, `opIndex :: Word32`,
   and the corresponding Coq primitive clauses and tuple encoding.
2. Output script bytes and `encodeHash . bslHash . txoScript`; reuse the
   annex/digest guards and shared conversion proofs. Do not claim host
   cryptographic implementation equivalence or caller cache construction.
3. The canonical current-outpoint program and library binding, shared literal
   indexed/current result definitions, and all six original/final full C
   contracts. Preserve failures and invalid-index behavior.
4. The complete outpoint environment representation: hash words, 64-bit C
   index equal to the unsigned 32-bit model index, input stride 544 and
   outpoint offset 96; output-script digest words at offset 180 within each
   248-byte output; input/output array/count offsets 0/696 and 8/704.

Source/negative and exact AST checks all passed. The guard rejected 48 in-memory
corruptions; independent supplementary review rejected 18 receipt/scope/status/
source/command/report/AST corruptions. A negative fixture exposed that a substring
carrier check accepted `int64` for `int`; the guard now compares the entire Coq
outpoint record, and that fixture passes. The proof and compiled objects were
unchanged. This is selected source correspondence, not a formal proof about the
host Haskell compiler, cryptographic library, or caller construction of caches.

```sh
python3 -B proof-work/elements-outpoint-output/review-source.py
python3 -B proof-work/elements-outpoint-output/test-source-review.py
```

These three jets are now ready to consider for a normal batch, alongside the
separately reviewed annex/optional-issuance work (possible combined successor
397/533 rather than 394/533). All snapshots, dependency/type diffs, exact
coverage negatives, full acceptance, and guarded source-only installation
still apply.

Main's live 378 actual-checkout audit (3224) and isolated 386 candidate audit
(87596) were both confirmed running during this checkpoint. Do not change
their inputs or start duplicate audits. Complete that prerequisite chain
before installing a successor. The full all-jet goal remains active.
