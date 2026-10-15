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

## Isolated acceptance passed; exact main installation completed

Session **53695** terminated with exit 0 after 3,215.00 seconds. The command
was exactly `bash check-jets.sh --accept`, without update/no-build/unchecked
flags. The normal build, all 978 kernel-checked modules, assumptions, contract
snapshots, negative tests and all five production AST regenerations passed.
`ACCEPTANCE.json` and `TERMINAL.json` bind the actual terminal result, log and
unchanged `7e55c862...` input fingerprint. A durable log is `acceptance.log`.

The prerequisite actual-main count acceptance also passed (recorded separately
in `../elements-count-admission/MAIN-ACCEPTANCE.json`). The one-time installer
then installed exactly seven metadata/snapshot files, four gate/printer
scripts, four selected guard files and two literal proof sources. It copied
no compiler objects. `INSTALLATION.json` and `DELTA.patch` bind this owned delta;
the complete original source map plus only that delta equals main's current
map. The original staged patch is unchanged, and main's full input fingerprint
exactly equals the accepted candidate's. Installed registration is **368/533**,
including the unchanged 104 explicit `memcpy_model` conditions.

The distinct actual-main sequence acceptance is now live as session **42404**,
launched by `main-accept.py`; `MAIN-AUDIT-RUN.json` records launch, not success.
Log: `/private/tmp/jet-sequence-admission.xtajlnf7/main-acceptance.log`.
Keep main Coq/C/Haskell inputs, registries, guards and snapshots frozen during
that run. Poll the actual handle for liveness; recorded identifiers alone do
not establish continued execution. Only a terminal `MAIN-ACCEPTANCE.json`
proves actual-main acceptance. The two completed predecessor runs must not be
restarted. Proof work can continue in independent external trees.

```sh
python3 -B proof-work/elements-sequence-admission/admission.py assemble
ulimit -s 65520
python3 -B proof-work/elements-sequence-admission/admission.py prepare /absolute/candidate
python3 -B proof-work/elements-sequence-admission/review.py finish /absolute/candidate
python3 -B proof-work/elements-sequence-admission/accept.py /absolute/candidate
```

Those phases are complete for the recorded tree. The guarded continuation is:

```sh
python3 -B proof-work/elements-sequence-admission/install.py /absolute/candidate
python3 -B proof-work/elements-sequence-admission/post-check.py
ulimit -s 65520
python3 -B proof-work/elements-sequence-admission/main-accept.py
```

Installation and main launch have already happened; do not rerun the one-time
installer or duplicate the live main audit. The installed-main postcheck has
passed with predecessor verification, exact source identity and staging
preservation; that precheck is not a substitute for terminal main acceptance.
Do not use the old count postcheck after this source change: it represents
its historical `aa2c4160...` source state. This batch's postcheck composes the
old source map, the exact new delta, and both terminal predecessor receipts.
Broader environment/evaluator composition and every other uncovered jet remain
work for the unchanged all-jet goal.
