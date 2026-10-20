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

## Isolated acceptance passed; exact main installation completed

The independent three-getter candidate is still undergoing full acceptance;
its tools require main's current source map to remain unchanged until their
terminal validation. Keep main's proof inputs frozen for that remaining run.
The getter installer requires both that terminal result and this actual-main
sequence receipt/postcheck; preparation or an active handle is not success.

Those phases are complete for the recorded tree. The guarded continuation is:

Installation and actual-main acceptance have already completed; do not rerun
the one-time installer or duplicate the completed audit. The installed-main
postcheck verifies both terminal receipts, exact source identity and staging
preservation. These receipts describe the actual staged/dirty checkout.
Do not use the old count postcheck after this source change: it represents
its historical `aa2c4160...` source state. This batch's postcheck composes the
old source map, the exact new delta, and both terminal predecessor receipts.
Broader environment/evaluator composition and every other uncovered jet remain
work for the unchanged all-jet goal.
