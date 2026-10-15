# Three Elements timelock jets checked under final C names

The checked roots are `C.jet_elements_is_final_local` and
`C.jet_elements_lock_literal`. They provide actual-C contracts for
`simplicity_tx_is_final`, `simplicity_tx_lock_height` and
`simplicity_tx_lock_time` against the canonical primitive Simplicity programs.
No mathematical predicate replaces the public specifications. The literal
lock program retains the Haskell word-conversion threshold and reuses the
two axiom-free generic program-matching bridges.

Private tree: `/private/tmp/jet-elements-timelock-normal.Jp0yB0`.
This is **preparation, not normal registration or full acceptance**.

## Isolation and verification

The source baseline is the reviewed direct-getter admission candidate at
`/private/tmp/jet-direct-getters-admission.yc45qogt`, whose full acceptance is
separate and was still running during this preparation. It is not described
as accepted merely because its source fingerprint matches.

Compiler objects and source copies came from the immutable, checked lock
tree—not from a running audit. Fifteen fixed source/metadata/guard inputs were
then read from the reviewed getter candidate to reconstruct its exact source
baseline. No live compiler object or other audit output was copied. Before
adding the one literal source, the full reconstructed input fingerprint was
checked against that reviewed baseline.

The literal source was copied byte-for-byte into
`C/jet_elements_lock_literal.v`; its text required no edit. Seven missing
dependency/root modules were freshly compiled under the final `C` namespace:

- `jet_elements_tx_field_set`
- `jet_elements_is_final_spec`
- `jet_elements_is_final_local`
- `jet_elements_lock_spec`
- `jet_elements_lock_exec`
- `jet_elements_lock_local`
- `jet_elements_lock_literal`

All 55 public helper/final result types and 31 definitions have untruncated
prints, with no unresolved placeholders. Per-result assumptions agree with
the previous checked source after renaming the private literal namespace.
Both generic source bridges are closed. Final endpoint assumptions remain
the same six inherited assumptions; there is no new library model premise.
Recursive kernel checking of both roots passed, with the unchanged library
context and no unsafe fixpoint/assumed-positivity categories. Regeneration of
the production Elements AST matched exactly.

The finality and lock source guards and their 31 + 32 negative source fixtures
also passed under final names. The evidence reviewer checks that all 1,579
inherited source files are byte-identical/in order-independent inventory;
only the one literal Coq source is added. The manifests, snapshots, coverage
and gate inputs remain exactly those of the reviewed baseline. Twenty-two
in-memory evidence mutations reject altered namespace, registration scope,
source inventory, closed-bridge evidence, compiler/checker commands, kernel
and AST logs. Invalid proofs are never compiled.

`PREPARATION.json` binds source and object bases separately, source-overlay
inventory, the original staged patch, exact compiler/checker commands, terminal
statuses, object/source hashes, reports and tools. Complete type/assumption/
kernel/AST reports and the literal source archive are retained here. These
receipts describe the actual dirty/staged source base, not clean-HEAD
reproducibility.

```sh
python3 -B proof-work/elements-timelock-normal/review.py
python3 -B proof-work/elements-timelock-normal/test-review.py
```

## Next admission

This batch adds **zero** registered jets. Main's current registration remains
368/533; its sequence actual-main audit has now passed. The separate getter
candidate proposes 371/533 and is still running. Poll the actual live handle
rather than starting duplicates. Keep main unchanged for that run's terminal
source validation.

The later `../elements-check-lock-normal/` preparation includes this entire
family plus both check-lock assertion jets under final C names. Prefer that
combined five-jet admission after the predecessor succeeds; retain this
smaller preparation as its historical prerequisite, not a competing batch.

After successful predecessor acceptance/installation, assemble a new normal
candidate from this final-name tree. Register the seven modules and their
55 results/31 definitions, but add jet coverage only for the three actual-C
canonical endpoints. Make both source guards and mutation suites mandatory.
Review inherited contract/dependency preservation and the complete new prints
before full `check-jets.sh --accept`, without skip/update flags. Installation
must bind that terminal result and the predecessor's actual-main acceptance,
copy sources only, and preserve all unrelated staged work.

Preserve the complete environment/frame/cursor/output/prefix/memory contracts
and the existing LP64/RECKLESS scope. This batch does not establish environment
builder/evaluator composition or assertion-enabled coverage. Every other jet
and outstanding conditional-library/caller obligation remains in the goal.
