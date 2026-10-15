# Normal admission candidate: Elements sequence jets

This batch proposes exactly `simplicity_input_sequence` and
`simplicity_current_sequence`, against their existing actual-C canonical
primitive/program contracts. The checked literal word-conversion bridges are
also registered as public results; no mathematical substitute or assumed C
execution is used. The input jet retains the separated `Word32 -> Sum Unit
Word32` contract and the current jet the plain `Unit -> Word32` contract, both
in `elements_ge` with the same formal environment, representation, output,
prefix, cursor and memory guarantees as their checked originals.

## Reviewed preparation

Candidate: `/private/tmp/jet-sequence-admission.xtajlnf7`.
Source/object base: the immutable, separately kernel-checked final-name tree
documented in `../elements-sequence-normal/README.md`, not main's live outputs.
Two new literal modules are included; sixteen existing dependency modules
have unchanged source. All eighteen are added to both normal manifests and
explicitly freshly compiled after the whole normal build.

The batch adds 98 public helper/final results and 41 definitions, including
the input decoder fixpoint. All 7,398 inherited contract records are retained
byte-for-byte/in order and all 4,896 inherited assumption sets are unchanged.
The 139 new records have complete checked reports and dependencies within the
six inherited assumptions. Four compact records require deep supplements:
`elements_wrapper_layout_simple`, `decode_wide32_unsigned`,
`indexed_scalar_rep`, and `current_scalar_rep`. They were compared against
their complete prints, not skipped.

The normal printer gains `Check @...` **only for these eighteen new modules**;
none has any inherited public record. This exposes the new generic parameters
without changing the printer treatment of old records. Deep reports reject
unresolved placeholders. The ordinary full `audit-jet-contracts.sh` comparison
passed on the candidate after this scoped change.

Coverage whitelisting adds only these two exact contract shapes. Twelve new
negative fixtures reject wrong C functions, linked/logical environments,
widths, whole-contract shape and vacuous premises. The selected source guards
and their 24 InputSequence plus 22 CurrentSequence mutations are installed in
the candidate's mandatory normal checker. Eighteen additional in-memory
admission corruptions reject altered registration, source, printer, snapshot,
assumption and terminal evidence. Invalid proof text is never compiled.

`ASSEMBLY.json`, `PREPARATION.json` and `REVIEW.json` bind all source/index
maps, exact deltas, compiler objects, reports, commands, successful exits and
review tools. Durable new-record reports are `new_contracts.log` and
`new_assumptions.log`. These describe the actual dirty/staged checkout,
including the existing shared word converter, not a clean-HEAD build.

## Full acceptance is running, not yet established

Session **53695** runs `accept.py` against the candidate. The command is
exactly `bash check-jets.sh --accept`, without update/no-build/unchecked flags.
It has reached recursive kernel checking; the full normal build and static
checks passed. `AUDIT-RUN.json` records launch only. Poll the actual session
for liveness; this file and its identifiers do not themselves establish it.
Log: `/private/tmp/jet-sequence-admission.xtajlnf7/acceptance.log`.

Keep the candidate's Coq/C/Haskell source inputs, metadata, guards and snapshots
frozen while this run is live. Do not change the three hash-bound preparation/
review tools either. Proof development can continue in separate external trees.
Only terminal exit 0, the unchanged fingerprint and the complete final marker
will produce `ACCEPTANCE.json`. The proposed **368/533** is not accepted/main
coverage at this milestone. Main remains **366/533**, with its own live count
acceptance in session **49451**; it too remains frozen.

```sh
python3 -B proof-work/elements-sequence-admission/admission.py assemble
ulimit -s 65520
python3 -B proof-work/elements-sequence-admission/admission.py prepare /absolute/candidate
python3 -B proof-work/elements-sequence-admission/review.py finish /absolute/candidate
python3 -B proof-work/elements-sequence-admission/accept.py /absolute/candidate
```

The first four phases and launch have already happened for the recorded tree;
do not restart either live audit. After both terminal acceptances succeed,
implement a one-time exact-delta installer preserving the original staged
patch, recheck the complete old map plus only this reviewed delta, and install
no compiler objects. A separate actual-main run remains necessary. Do not use
the old count installer's pre-installation baseline checks after changing main;
the next batch needs its own preservation ledger. Broader environment-builder/
evaluator composition and every other uncovered jet remain separate work.
