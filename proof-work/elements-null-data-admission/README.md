# Isolated contextual null-data admission (candidate 419)

Candidate: `/private/tmp/jet-null-data-admission.i6xxdcrl`.
Baseline: the actually accepted main **418/533** tree, identical in semantic
inputs to `/private/tmp/jet-txid-admission.gvp5bmft`.

Preparation has completed successfully. The full build and all 24 explicit
fresh compiles exited zero. The new audit inventory has 144 theorem results
(61 closed) and 103 definitions, including the constructors of the inductive
parser relation. All fresh dependency sets equal the checked proof batches;
the complete C endpoint has only the six inherited assumptions. Full build,
deep/compact type-definition and assumption reports are archived here.

This is **not full acceptance**. At this checkpoint the independent normal
review is running; neither installation nor a 419th accepted main jet is
claimed. `REVIEW.json`, then `ACCEPTANCE.json`, must supply actual successful
terminal evidence before their corresponding milestones can be claimed.

## Proof and source boundaries

The candidate imports the exact sources from 17 individually checked proof
batches. Their receipts remain separate and immutable. The later source review
is separately bound through
[`../elements-null-data-source/SOURCE-REVIEW.json`](../elements-null-data-source/SOURCE-REVIEW.json),
not retroactively asserted in older formal receipts.

The coverage endpoint is
`C.jet_elements_null_data_literal.elements_output_null_datum_literal_bitmachine_spec`.
It executes the complete actual C function against the selected canonical
`Elements.OutputNullDatum` primitive, with an additional checked literal
encoding/indexing bridge to the reviewed Haskell clauses.

Its public contract is explicitly `application_jet_bitmachine_spec`, on
represented, separated Bit Machine frames, with unchanged active/inactive
read frames and inactive writes. The environment relation is input-independent
and includes parsed opcode/cache coherence. No arbitrary overlapping-buffer
claim, real environment-builder establishment, assertion-enabled build proof,
or formal Haskell/host-library equivalence is added.

The exact new family is admitted only for this named jet, linked program,
logical environment, input/output types, representation and literal spec.
Negative coverage tests reject alternate contracts, widths, environments,
specifications and hidden preconditions. The shared contract, environment
predicates and parser relation are also in the definition audit.

## Tools and preservation

`normal-delta-prepare.py` is unchanged. `normal-delta-review-v3.py` preserves
the v2 review logic except for two explicit interfaces: a map of individual
proof/source evidence receipts instead of one synthetic aggregate receipt,
and an explicit selected-source-check hook. v2 remains unchanged for historical
reviews. The new admission boundary validates the actual418 installation and
acceptance plus every new batch's compiler/kernel/report/evidence logs,
source/object bindings, declarations and checker/reviewer identities.

The seed proof tree omitted 16 deployed source-guard scripts present in the
normal418 baseline. The initial assembly check rejected this before recording
an assembly. The same private seed was resumed with that exact missing-guard
inventory recognized; all baseline scripts were restored from accepted418.
No inherited proof source is replaced, and no proof object is installed in main.

Main semantic inputs and the original staged patch remain unchanged. The
staged patch identity is
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.
Like the predecessor evidence, receipts bind the actual dirty source trees;
they do not assert clean-HEAD reproducibility of unrelated staged work.

## Continue the recorded candidate

Do not assemble or prepare another copy while the recorded run is live.
Read-only review (after preparation):

```sh
python3 -B proof-work/elements-null-data-admission/review.py review /private/tmp/jet-null-data-admission.i6xxdcrl
```

After successful independent review, launch the full acceptance once:

```sh
python3 -B proof-work/elements-null-data-admission/accept.py /private/tmp/jet-null-data-admission.i6xxdcrl
```

That runs `bash check-jets.sh --accept` with no update/skip flags, records the
terminal exit/log, checks the full acceptance marker and revalidates the exact
reviewed source/evidence/index. Keep candidate sources frozen throughout it.
Guarded main installation and a real main-tree audit remain separate later
steps. Main coverage must remain reported as 418 until those steps pass.
