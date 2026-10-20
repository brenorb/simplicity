# Indexed/current Elements pegin contracts under final C names

Both actual C jets (`simplicity_input_pegin` and `simplicity_current_pegin`)
now have their checked canonical-source bridges under the normal
`C.jet_elements_pegin_literal` namespace. The literal proof is byte-identical
to the previously checked private-namespace source in `../elements-pegin/`.
The primitive is an optional digest, not bytes to hash or a Boolean. The
indexed contract retains both presence tags; the current-input contract
retains the canonical assertion that removes the outer tag.

The original separated frames, arbitrary output contents, cursor/prefix,
environment representations and permitted-memory-change contracts are
unchanged, as is the LP64/RECKLESS build scope. These results do not prove
environment-builder/evaluator composition or assertion-enabled builds.
Receipts bind the actual dirty/staged source base, not a clean-HEAD build.
The full all-jet objective remains unfinished.
