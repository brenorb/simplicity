# Issuance blinding entropy: original C and literal canonical program

Current-source qualification: the earlier incremental build did not establish
that every imported object matches its current source. A stale imported Bitcoin
object was subsequently found. Preserve these kernel receipts as evidence for
their exact compiled inputs, not a completed restored-source rebuild. See
`../original-target-boundary/` and the separate forced rebuild in
`../elements-hashes-clean/`. This qualification governs the older statements
below; no historical receipt is overwritten.

The endpoint to use for future admission is
`BlindingCanonical.BlindingEntropy.elements_issuance_blinding_entropy_hash_literal_local_spec`
in `canonical/BlindingEntropy.v.source`. It is a complete original-C getter
execution theorem against the primitive-based canonical program, conditional
on the explicit initial cached-hash/environment relation and valid separated
frames. It does not prove that the production environment builder establishes
that cached hash. No normal registration or coverage is added here.

`verify.py compile|kernel PRIVATE_TREE` rebuilds/checks the intermediate
chain. `canonical.py compile|kernel PRIVATE_TREE EXTERNAL_TREE` checks the
literal companion in the narrow `BlindingCanonical` namespace, without
altering the frozen base tree. The existing receipts are once-only: inspect
them and the original process before starting another run. A new input needs
new evidence, not relabeling an old successful receipt.
