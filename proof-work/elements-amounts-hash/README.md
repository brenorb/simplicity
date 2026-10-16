# Shared Elements input/output amounts-hash C proofs

Private tree: `/private/tmp/jet-elements-amounts-hash.66_lhzdf`, cloned from
the completed immutable nonce proof tree. No inherited source, normal registry,
production C/header, canonical Haskell program or original staging is changed.

The two complete endpoints are
`elements_output_amounts_hash_program_local_spec` and
`elements_input_amounts_hash_program_local_spec`. They prove the original
generated C getters in `elements_ge` against their primitive-based Simplicity
Transaction amount-pair program followed by `assetAmountHash`, the checked
32-bit hash loop and SHA finalization. They are not merely equalities between
specifications.

The shared serializer retains the canonical encodings:

- asset: prefix 10/11 and 32 bytes for a confidential value, or prefix 1 and
  32 bytes for an explicit value;
- amount: prefix 8/9 and 32 bytes for a confidential commitment, or prefix 1
  and 8 bytes for an explicit Word64 value.

The tagged-byte absorber is reused unchanged from the checked nonce package.
The canonical `elements_amount_pair_spec` and its input/output semantics are
reused unchanged from the existing C amount-jet proof. A single parametric
hash-loop theorem and C getter-execution adapter then serve both endpoints.
The field offsets24 and248 and structure size760 are discharged against the
actual generated composite environment in Coq, not assumed.

`RUN.json` binds fresh Coq8.17.1 compilation of both modules and the full
22 result/23 definition reports. Sixteen results are closed, three reuse
inherited functional extensionality, and the generic C adapter plus both
endpoints retain the same six inherited assumptions as the checked getter.
The reader-semantic results use the existing amount-pair semantic lemmas;
they are not claimed to be closed when those dependencies use extensionality.
The axiom allowance is unchanged.

Boundary: `hash_getter_rep` is an explicit caller relation between cached C
hash words and the logical environment's canonical digest. This package does
not establish that cache through the real transaction builder. Confidential
coordinates use the existing packed-field projection interface; no assertion
that every arbitrary word is a valid field element is added. No execution,
output or framing conclusion is moved into a new final-theorem premise.

The once-only kernel/AST phase was launched under session62838. Inspect that
actual handle and terminal receipt before any restart. Canonical source review,
recursive kernel completion, evidence review and normal registration remain
distinct from compilation; no accepted coverage is added by `RUN.json`.

```sh
python3 -B proof-work/elements-amounts-hash/check.py /private/tmp/jet-elements-amounts-hash.66_lhzdf
python3 -B proof-work/elements-amounts-hash/kernel.py /private/tmp/jet-elements-amounts-hash.66_lhzdf
```

The drivers refuse to overwrite completed receipts. Both archived source
modules compile completely through their final `Qed`; there are no unfinished
proof declarations or skipped proofs in this checkpoint.
