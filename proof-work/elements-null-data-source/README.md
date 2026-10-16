# Null-data selected-source review

This batch completes the selected-source correspondence review for the checked
`simplicity_output_null_datum` implementation-to-primitive proof. It adds **no
normal registration or coverage**. Main remains the accepted 418/533 tree.

The immutable formal receipt is
[`../elements-null-data-literal/EVIDENCE-REVIEW.json`](../elements-null-data-literal/EVIDENCE-REVIEW.json).
Its source-gate flag remains false: that receipt predates this review.
`SOURCE-REVIEW.json` separately binds that evidence, current sources/objects,
all recorded compiler/kernel/AST/report commands, the current main/index, and
the source checkers and their inherited checker code.

Reproduce the read-only review:

```sh
python3 -B proof-work/elements-null-data-source/review.py verify /private/tmp/jet-null-data-literal.lh3EDxlD
```

## Reviewed correspondence

- The Haskell jet dispatch selects `Prim.OutputNullDatum` in the `Elements`
  namespace, with two 32-bit indices and the expected nested sum result.
- The complete Haskell datum parser and Coq port agree on OP_RETURN, all
  opcode alternatives, immediate lengths, little-endian length fields,
  failed/truncated parses, and the successful empty remainder. The formal
  fuel-adequacy theorem establishes that the Coq port's byte-length fuel
  implements its unbounded successful-parse relation; every accepted datum
  consumes an opcode byte, even an empty immediate push.
- All 22 Haskell encoding clauses correspond to the literal Coq encoder.
  Shared checked word-conversion/hash-decoding lemmas handle the indices and
  digest output. The selected byte-string SHA wrappers are pinned too.
- The whole C function, complete canonical/literal endpoint statements,
  input-independent environment relation and shared contextual frame contract
  are pinned, not merely a matching fragment in an unrelated theorem.

`source-model.py` contains readable, fixed expected active declarations and
clauses. The checker strips comments and rejects missing/ambiguous boundaries.
`test-source.py` rejects 113 targeted changes to the parser, encodings,
environment, whole contract, C branches, hash wrapper and parser import/binding.
The recorded positive and negative commands both exit zero. This is a
regression guard around a source review, **not a second proof checker**.

## Boundaries

The formal endpoint executes the complete pinned assertion-disabled Elements
Clight function and preserves represented, separated Bit Machine frames. It
does not establish an unrestricted overlapping-buffer API contract. The
overlap diagnostic remains documented separately in
[`../null-data-overlap-probe/README.md`](../null-data-overlap-probe/README.md).

The physical environment relation requires parsed opcode/cache coherence with
the logical scripts. Establishing that relation from the real Elements C
environment builders is still separate work. There is no formal equivalence
proof here for the Haskell runtime, `Data.Serialize.Get`, byte-string libraries
or the host SHA library. The checked Coq parser/encoder/literal bridges and C
execution theorem are genuine formal proofs; the selected Haskell-to-Coq
source correspondence is an explicit reviewed boundary.

Next: assemble an isolated normal candidate with the explicit contextual
contract family, full declaration/definition audits (including the inductive
parser relation), negative coverage tests, then full acceptance. Do not count
this source review alone as the 419th accepted jet.
