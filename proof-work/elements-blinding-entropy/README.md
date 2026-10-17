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

Both `CHECKED.json` and `CANONICAL-CHECKED.json` record successful recursive
kernel checks for their exact compiled objects. They do not bind all imported
objects to the restored sources; the qualification above applies to both.
The latter includes the literal canonical serializer prefix: Haskell uses
`one word8`, ported using the existing polymorphic `one8_spec`. The intermediate
serializer in `source/` uses a constant-one scribe. Its checked endpoint is
useful support, but the literal adapter is the final canonical endpoint; they
are not two different jets and must not be counted twice.

The reader is the canonical three-primitive
`issuanceBlindingEntropy` program, built from NewIssuanceContract,
ReissuanceBlinding and ReissuanceEntropy. Missing input, no issuance, new
issuance (zero blinding nonce and contract), and reissuance (blinding nonce
and entropy) are handled by the original nested cases. The hash program uses
the checked 32-bit reader loop, original ctx8 primitives and finalization.
No C, original specification, primitive identity, API or generation setting
was changed. `AST-CHECKED.json` records direct regeneration of the unchanged
Elements AST with the pinned configuration.

`RUN.json`, full type/definition/assumption reports, `KERNEL-RUN.json`,
`CHECKED.json` and their `CANONICAL-*` counterparts bind the source/object
identities and process outcomes. The intermediate chain has 14 results and
14 definitions; the literal companion has six results and two definitions.
The endpoints use the six inherited dependencies of the existing Clight
chain; pure/parametric results introduce no new assumptions. Nothing is
admitted or kernel-check-disabled.

`verify.py compile|kernel PRIVATE_TREE` rebuilds/checks the intermediate
chain. `canonical.py compile|kernel PRIVATE_TREE EXTERNAL_TREE` checks the
literal companion in the narrow `BlindingCanonical` namespace, without
altering the frozen base tree. The existing receipts are once-only: inspect
them and the original process before starting another run. A new input needs
new evidence, not relabeling an old successful receipt.
