# Two composite Elements hash getters

Current-source qualification: the earlier incremental build did not establish
that every imported object matches its current source. A stale imported Bitcoin
object was subsequently found. Preserve these kernel receipts as evidence for
their exact compiled inputs, not a completed restored-source rebuild. See
`../original-target-boundary/` and the separate forced rebuild in
`../elements-hashes-clean/`. This qualification governs the older statements
below; no historical receipt is overwritten.

The complete original-C endpoints are
`elements_outputs_hash_program_local_spec` and
`elements_input_utxos_hash_program_local_spec` in the archived
`source/jet_elements_composite_amounts_hash.v.source`. `CHECKED.json` records
successful recursive kernel checking against the exact compiled objects, not
a fully source-bound rebuild of the restored Bitcoin specification. These are not new
normal-registry/coverage entries or a full acceptance of the repository.

The targets are the primitive-based canonical outputsHash/inputUtxosHash
programs, reusing the checked amounts, nonces, script and range-proof hash
programs. A shared fixed-vector hash skeleton handles four hashes (128 bytes)
and two hashes (64 bytes), with the original ctx8 add/finalize primitives.
Actual getter calls, outputs, cursor advancement and framing are derived.

The explicit initial relations assert the corresponding cached hash at
transaction offset 184 (outputsHash) or 312 (inputUTXOsHash), in the original
760-byte transaction layout. This package does not prove that the production
environment builder computes those caches correctly. It does not change C,
the original specifications/API or generation settings, and does not assume
an execution or its output to obtain the final result.

`verify.py compile|kernel PRIVATE_TREE` checks the archived sources against a
distinct current-source clone, rebuilding dependencies without editing the
project manifests. Full eight-result/five-definition reports and exact
assumption checks accompany source/object hashes. Both endpoints retain the
six inherited dependencies of the existing Clight chain. Historical evidence
is not transferred to changed inputs; existing receipts cannot be overwritten.
