# Original calculation jets from actual initial memory

This extension uses the actual original Elements initializer to establish the
SHA compression dispatch pointer. The shared frame-construction proof then
builds readable input and writable output frames for every Word256 input while
preserving initial global loads. The three `calculate_*_initial_run` results
invoke the enclosing C-to-canonical-Simplicity contracts and preserve all loads
of the original initial-memory blocks. No represented-frame or dispatch premise
remains in these three results. `memcpy_model` remains explicit.

The generic initializer-checking prefix is reused from
`Coq/C/jet_sha_startup_init.v`; no SHA-specific startup result is imported as
an Elements execution fact. Closed checks target `jets_elements.prog` itself
and prove its initial memory exists, so the initial-memory premises are
inhabited. This does not replace the more general local contracts, constrain
their arbitrary cursors/output contents, or prove correctness of any evaluator.

These are unregistered proof-support results, with zero added accepted coverage.
No production C, original specification, API or generation setting is changed.
