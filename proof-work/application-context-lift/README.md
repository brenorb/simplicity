# Shared application-contract → Bit Machine lifting

Three new complete results have been freshly compiled and recursively
kernel-checked, with full type and assumption reports. All three have only
the six inherited execution assumptions. Independent evidence review passed,
including 22 read-only corruption tests and a separate terminal postcheck of
the sources, fresh objects, command exits/logs, tools, reports and receipts.
There are no new definitions, library models or registered jets.

## What is proved

`application_jet_local_sep_to_bitmachine` turns an existing complete
`application_jet_local_spec_sep` theorem into
`application_jet_bitmachine_spec`, for any linked global environment, logical
environment type, input/output Simplicity types, representation and spec,
provided the output has at least one bit.

The proof extracts input cursor/alignment/encoding facts from `bm_rep`, obtains
the writable output-frame contract from represented writable frames, invokes
the existing whole C-function theorem, and uses its output/prefix/cursor/load
guarantees with `bm_rep_after_write`. The result preserves all inactive frames
and the active read frame while appending the encoded result to the active
write frame. It does not assume the desired C execution or final state.

Two concrete uses discharge the local-contract premise with existing proofs:

- Elements `input_sequence`: 32-bit input and 33-bit optional output, with its
  existing literal canonical-specification bridge and indexed environment.
- Bitcoin `script_cmr`: unit input and 256-bit output, retaining its original
  Bitcoin primitive semantics and environment relation.

The examples' final statements have no extra arrow premise. Positivity is
discharged by the concrete output types. No new C-to-specification coverage is
claimed for jets that were already registered.

## Reuse and limits

Future nonempty-output application jets can first prove the familiar local
contract and then obtain the stronger contextual frame theorem with this
shared result. Zero-bit outputs and partial/failing-jet contracts are not
covered by this helper and are not silently redefined.

For input extraction, this batch reuses the already checked generic
`bm_active_read_encoded_prefix` lemma currently housed in
`C.jet_elements_null_data_bitmachine`. This creates a module dependency on that
file, but no hypothesis about Elements or its C function in the shared theorem.
Moving that generic helper into a neutral module would be a later reviewed
refactor, not an edit to the frozen419 candidate here.

All physical environment premises and their output-footprint separation remain
explicit. Actual C environment-builder establishment, broader aliasing APIs,
assertion-enabled builds and full acceptance/registration are not added.
