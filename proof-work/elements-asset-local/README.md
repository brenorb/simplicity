# Complete original asset_amount_hash C-to-Simplicity equivalence

`Actual.asset_amount_hash_local_spec` proves the actual original
`jets_elements.f_simplicity_asset_amount_hash` call in `elements_ge` against
the literal `Spec.elements_asset_amount_hash_spec`, interpreted in `optalg`.
This includes function entry, source-frame copying, real SHA initialization and
context parsing, all asset/amount branches, final context writing, return-value
conversion and freeing all four actual locals. It is not only a relationship
between specifications or a C helper byte-stream result.

The input is 1346 bits and the output context is 830 bits. Arbitrary valid frame
cursors, boundary crossings and existing output bits are supported. Confidential
payloads are unrestricted Word256 values; explicit amounts are unrestricted
Word64 values. Invalid initial compression counts and final overflow both
return false, exactly as the canonical option semantics requires. Successful
calls write the canonical encoding, preserve preceding output bits, update the
output cursor, and preserve loads outside the allowed output ranges.

Conditional boundaries remain explicit: the existing `memcpy_model`, actual
Elements dispatch/maximum-counter loads, and the ordinary readable-input and
writable-output frame contracts. No desired execution, intermediate SHA state
or output is assumed. Initial-memory/frame construction is not yet a corollary
of this packet. The theorem concerns the original generated Elements program;
it makes no additional host-library or assertion-enabled-build claim.

## Reuse and fidelity

The already checked nonce lifecycle supplies the generic frame contract and
source-copy derivation. The asset and amount packets supply the actual middle
execution, exact function body/entry and statement-sequence composition.
`Bridges` connects their byte lists to the pre-existing canonical serializers.

The four existing pure specification modules (`Buffer`, `ContextHashes`,
`TaggedWord`, `Spec`) are freshly recompiled in the new external tree. Only their
import qualifications change; all definitions and proof bodies are preserved.
`verify.py` checks that exact transformation, the reviewed canonical Haskell
regions/catalog binding/original C body, and all eight archived proof digests.
This is an explicit literal-source review, not a formal Haskell translation
theorem. No original specification, production implementation, API or generation
setting is changed.

`Counter.sha_chain_overflow` is reusable for bounded successive additions. It
covers crossing the maximum at an intermediate addition through the real sticky
overflow flag. Its specialization combines all four asset/amount additions into
42 or 66 bytes; it does not assume the intermediate asset phase remains valid.
The actual `_t'6` result temporary and 16/32/32/88-byte local allocations/free
order are retained in the full function proof.

## Verification

Place the eight archives in a fresh external directory as `Buffer.v`,
`ContextHashes.v`, `TaggedWord.v`, `Spec.v`, `Counter.v`, `Bridges.v`, `Local.v`,
`Actual.v`. The driver freshly compiles all eight files, reports full
types/definitions/assumptions, checks exactly forty results and twenty-six
definitions, binds 260 local imports to their forced source/object provenance,
and verifies sixteen inherited external modules. Thirty-seven new results are
closed; the global-state equivalence has four inherited dependencies; the two
full C-call theorems have the six inherited CompCert/VST dependencies. The
explicit `memcpy_model` premise remains conditional, not discharged by this
assumption report.

Unregistered proof work: accepted coverage added is zero. Full-repository jet
coverage, normal admission and the existing external-library obligations remain
unfinished.
