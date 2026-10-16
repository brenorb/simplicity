# Validated null-data jet API aliasing discrepancy

This follows the earlier `../null-data-overlap-probe/` observation at the user's
request to validate the API edge before further whole-jet composition. It adds
zero equivalence coverage and changes no production C, header or specification.

## What is now reproduced

The fixture uses the **actual** `simplicity_elements_mallocTransaction`,
`simplicity_elements_mallocTapEnv` and `simplicity_elements_build_txEnv`, not a
hand-filled transaction/cache structure. The real transaction builder parses
the output script bytes `6a 51` (`OP_RETURN OP_1`) into one OP_1 datum. The
environment has one input, one output, current index zero and a well-formed
empty tap path. The public raw-buffer construction requirements are satisfied;
this does not claim validation of a consensus transaction or taproot spend.

Both original logical indices are checked to be `(0,0)` immediately before
calling the unmodified `simplicity_output_null_datum`. Each input frame has64
initialized cells; each output frame has261 initialized writable cells.
The descriptors and environment do not alias the data. Only the backing input
and output slices overlap in the failing case.

All eight AddressSanitizer + UndefinedBehaviorSanitizer configurations reproduced
the same discrepancy: native16-bit / explicit64-bit UWORD, debug / PRODUCTION,
and `-O0` / `-O2`. No sanitizer error was reported (not a proof of universal UB
absence; leak detection is disabled because this is macOS). Every run also
passed two controls: separate backing arrays and disjoint slices of the same
array. Thus eight failing-overlap cases and16 passing controls are recorded.

Expected original-input tags: `1,1` (output present, datum present).
Observed overlapping-call tags: `1,0` (output present, datum absent), despite
success and the destination cursor reaching zero. The64-bit case leaves the
source indices `(0,16)`; the16-bit case leaves `(0,1048576)`.

The source order in `C/elements/elementsJets.c` is `read i; write outer tag;
read j`. The first tag sets a bit in the unread second index. In the64-bit
fixture that is bit4 of the source word, changing the would-be `j` from0 to16.
The jet subsequently tests that changed index against the one-element datum
array. No assertion, malformed parser result or fabricated environment explains
the difference.

## Contract classification

This is a confirmed **native stand-alone API aliasing discrepancy**. If the
individually-valid-frame preconditions listed in `C/jets.h` are intended to be
sufficient, it is an implementation-to-specification mismatch for that broader
API domain. `C/jets.h`, `C/frame.h` and the Elements jet header do not explicitly
state input/output non-overlap. They do not give a formal definition of
"valid frame" from which an implicit ownership restriction can be settled.

It is **not** a counterexample on valid evaluator layouts. `C/eval.c` organizes
read/write word slices as opposite sides of a gap buffer and checks the active
read edge does not exceed the active write edge before dispatch. The formal
`bm_separated` relation states the corresponding separation. Both disjoint
same-allocation controls pass; block identity alone is not the relevant issue.

The remaining design decision is explicit: document the evaluator's non-overlap
invariant as part of the stand-alone jet API, or change the implementation to
support the broader aliasing domain. Neither choice is silently made by these
tests or by strengthening a proof premise. No C/header fix is authorized or
performed here.

This native test is Apple clang/arm64 execution, even when UWORD64 is selected.
It is not a proof of the pinned CompCert Clight call, not an ABI-equivalence
proof, and not evidence of a reachable production-evaluator/consensus failure.
The separate formal reference checks validate the canonical expected result,
not the native C execution. Do not label them a formal Clight counterexample.

## Reproduce and inspect

Native private tree: `/private/tmp/jet-overlap-validation.glob2m5c`.
Exact committed fixture: `probe.c.source`.

```sh
python3 -B proof-work/null-data-overlap-validation/check.py /private/tmp/jet-overlap-validation.glob2m5c
```

The once-only run completed under handle45553. `VALIDATION.json` and exact
compiler/build/run logs record source identities, all command/exit statuses and
outcomes. Exit zero means the discrepancy reproduced with passing controls,
not successful equivalence. The driver refuses to overwrite the receipt.

Main semantic fingerprint stayed
`c30bd6ac82c17410b9315a9e06d8b026294434a96180612bd717e7e4c8a64f21`;
the original staged patch stayed
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.
The separate live full447 and SHA-adapter audits were not changed or restarted.
