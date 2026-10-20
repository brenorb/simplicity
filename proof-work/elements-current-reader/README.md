# Current-frame readers and unread-input preservation

## Formal progress

`C.jet_elements_current_reader` reuses the existing verified core readers and
Elements transport to prove calls on an **already initialized** frame. It does
not require another allocation/source-copy step. The generic theorem covers
16/32/64-bit readers and retains the exact returned unsigned value, advanced
cursor, unchanged non-cursor loads, permissions and valid blocks. The concrete
read32 statement theorem includes the actual helper call and following Sset,
with the exact two temporary updates. Closed source equalities tie the two
instantiations to the existing first read and the actual second read of
`simplicity_output_null_datum`.

`C.jet_read_after_write` discharges the read-after-write boundary identified in
the preceding batch. It proves:

- A `write_effect` preserves specified unread input bits when their actual
  machine-word loads avoid the output effect.
- Closed arithmetic bounds place each read word inside its complete read-frame
  slice and each output effect inside the write-frame slice.
- The existing `bm_rep`/`bm_separated` predicates imply that separation for the
  active frames, using their word ranges and distinct frame/data allocations.
- Therefore an arbitrary unread active-read suffix survives the output effect.
  **Read and write data use the same `cells_blk` in this theorem.** No premise
  requires distinct input/output data blocks, zero padding or aligned cursors.
- A fresh private read-frame header and its writable cursor permission survive
  an output effect, providing the other preconditions of the next reader call.

This is a formal range/preservation proof, not an informal appeal to evaluator
comments. The observed C evaluator gap-buffer organization agrees with the
existing word-separated invariant; proving that the C evaluator establishes
and maintains that invariant remains a separate obligation. The theorem uses
the existing formal predicates, not an assumed result of the desired reader
execution. Actual execution is still derived from the represented input bits.

The next caller must instantiate these shared lemmas for its source copy and
unread second32-bit word, transport its environment/output relations across
the actual local-cursor update and compose the checked guard/index blocks.
No whole-jet endpoint, coverage entry or normal registration is added.

## Verification checkpoint

Development corrections were explicit conjunction construction (instead of
over-splitting a frame predicate) and specifying cursor/count before arithmetic
in the suffix-preservation application. No theorem domain or implementation
changed.

## Continue

Use `eval_elements_current_reader` / `exec_elements_read32_current` for the two
actual source reads. For the second, derive unread-input preservation across
the first tag with `write_effect_keeps_active_read_suffix`; derive the private
header and permission conditions with the two final lemmas. Account for the
read's modification of its private cursor when composing `write_effect`s back
to the initial memory. Then compose the outer guard, conditional second read,
260-bit index block or260-bit absence padding, first read and function
entry/free into the complete261-bit result. Keep canonical parsed-script/hash
caller relations, empty arrays, assertion configuration and canonical source
review explicit.
