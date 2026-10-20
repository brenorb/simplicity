# Native overlapping-frame discrepancy: review boundary, not accepted proof

This diagnostic tests a scope distinction exposed while proving
`simplicity_output_null_datum`. It contributes **zero proof coverage** and is
not a Coq/CompCert execution counterexample or an informal substitute for one.
No implementation/specification/header was edited to make this test pass.

Follow-up: `../null-data-overlap-validation/` now reproduces the discrepancy
using the real transaction/taproot/txEnv builders and parser, with eight
sanitizer-clean native configurations and16 passing disjoint controls. That
removes the manual-environment limitation of this original probe; it still
does not establish a formal Clight or evaluator-valid counterexample.

## Observation

The `C/jets.h` jet interface lists valid source/destination frames and non-null
environment as preconditions, but does not explicitly state that the backing
slices must not overlap. In contrast, the C evaluator's gap-buffer organization
uses disjoint read/write word slices, and the existing formal `bm_separated`
predicate states that separation.

The archived `probe.c.source` calls the **actual** `C/frame.c` and
`C/elements/elementsJets.c` with original indices i=0,j=0 and one parsed output
datum OP_1. All frame data is initialized; the source has64 cells and the
destination261. A disjoint-buffer control produces the expected present/present
tags1,1. An overlapping layout produces1,0 instead, while returning success and
advancing the destination to its end. The first output tag is aligned with an
unread part of the second input index.

The mechanism matches the actual source order: read i; write the outer tag;
then read j. Overlap allows that tag write to alter j before the jet reads it.
The mathematical/primitive case being represented is a null-data script
OP_RETURN OP_1, at output0 and datum0. The existing checked primitive bridge
encodes that case as two present tags, not the absent-datum result observed in
the overlapping run.

## Limits and required follow-up

- This is an Apple clang/arm64 native diagnostic, not execution of the pinned
  CompCert Clight AST. Selecting UWORD64 matches the formal word width but does
  not make native ABI layouts identical to that AST's target.
- The fixture initializes the environment fields used by this jet manually.
  It does not invoke the complete real transaction/taproot environment builders;
  unused cached fields are zero. The two runs use the same fixture, and the
  inspected jet reads only the represented count/null-data/opcode fields, but
  this is not a proof of full environment-builder correspondence.
- The overlapping layout deliberately violates `bm_separated` and is not a
  counterexample for a valid evaluator state. No production-evaluator failure
  has been established.
- Accordingly, treat this as a concrete native **API-aliasing discrepancy /
  candidate broader-contract mismatch**, not a confirmed failure of canonical
  implementation-to-specification equivalence on valid Bit Machine states.

Before claiming a theorem for every layout admitted by the header's wording,
validate the domain using a fully constructed environment and/or a formal
counterexample. Then decide explicitly whether the interface requires the
evaluator's non-overlap invariant or whether the implementation should support
overlap. Do not silently strengthen a required universal contract to hide this
case. Changing C or its documented interface is a separate reviewed decision;
neither was done here, particularly while actual-main418 audit6155 is frozen.

The valid-layout Coq work continues independently: the reader/preservation
lemmas derive unread-input preservation from actual formal word-range
separation, with input/output data in the same allocation. Those checked
results do not claim arbitrary overlapping-buffer correctness.
