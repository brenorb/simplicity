# Complete original scalar_multiply jet against its literal specification

`OwnC.jet_secp_scalar_multiply_local.scalar_multiply_literal_local_spec`
proves the **complete original public C jet** against the existing literal
`canonical_scalar_multiply` Simplicity Core program. The final root has the
ordinary general frame/input/cursor preconditions of `secp_jet_local_spec`.
It has no normalized-input, arithmetic value, helper execution, output,
post-memory invariant, allocation or free premise.

The actual function entry, three outer-local allocations, source-struct copy,
two scalar readers/normalizations, in-place multiplication and its private
scratch lifecycle, scalar writer and its private buffer lifecycle, true return
and all outer-local frees are derived. The conclusion includes exact encoded
output, preserved write prefix, output cursor advancement and permitted memory
changes. Output memory is not assumed initially zero, and cursors are not
restricted to a special aligned layout.

The specification remains the literal `mul256 >>> scalar_normalize512` term
from `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs` (lines 410-411 and 586).
The existing Coq port is unchanged. Numeric modulo identities are internal
bridges connecting the actual computation to that term, not substitute public
specifications or independent mathematical certification.

This is one checked **public proof candidate**, not main-registry acceptance.
No C, specification, registry or acceptance snapshot is changed here. It adds
zero to this checkout's accepted coverage until isolated promotion and the
integrated gate pass. The complete all-jet goal remains unfinished.
The existing LP64 RECKLESS (assertion-disabled) build is retained; other build
configurations are not newly established by this milestone.

## Ownership and reuse

The new body/function proofs retain b's Freeable permission from the actual
post-product representation, through the reducer's outside-`[a,l]` frame and
the real scratch free. The same actual final memories/executions are used;
two existential function witnesses are not assumed equal. The writer then
preserves b and the source-local frame, enabling the real outer cleanup.

Scalar-add's existing general reader support and two-reader composition are
reused (only namespace/audit-footer adaptation for the latter). The public
entry/copy/body/lifecycle pattern is adapted to the **actual multiplication
AST**, with a void scalar_mul helper result, not addition's integer result.
Closed source-body equality and actual global-environment linkage lemmas are
included. Promotion should share the reader and generic writer modules with
the scalar-add candidate rather than permanently duplicate them.

Public multiply covers every Word256 pair, including equal values. Public
square is still separate: it calls the helper with the **same input pointer**
twice, whereas multiply's two scalar locals are distinct freshly allocated
blocks. Do not confuse equal input values with that pointer-alias case.

## Verification

Terminal build/kernel records and hashes are in `REVIEW.json`. All 14 modules
and both drivers were freshly rebuilt after correcting inherited comment
labels, then frozen for independent kernel checking. The initial and final
contract/assumption reports agree byte-for-byte. There are 29 result types,
six new definitions and three additionally printed critical definitions:
the public frame contract and the two literal specification terms. The full
contract report has 94,535 bytes and no truncation.

Six results are closed. Six representation results retain four inherited
classical/extensionality dependencies; 17 execution results retain the
inherited six dependencies including CompCert's two semantic parameters.
No new axiom or skipped proof. The inherited dependency-wide kernel context
is checked separately, with the expected 15 axioms and no unsafe categories.

Production/canonical source identity passed for 240 files, and the immutable
dependency fingerprint is unchanged. Full AST regeneration and integrated
acceptance were **not** run. Sources/drivers are durable here; compiled
objects, reports and terminal-run logs remain local in the recorded scratch.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-multiply-public/review.py
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-multiply-public/test-review.py
```

Rebuild using the Coq 8.17.1 / OCaml 4.14.4, CompCert 3.14, VST 2.14 setup
from `../scalar-mul-function/README.md`, with the additional narrow mappings
`/tmp/jet-scalar-mul-public.nzHcef` to `PubC` and
`/tmp/jet-scalar-mul-ownership.Ste5AV` to `OwnC`. Run the 14 modules in manifest
order with `build-jets.sh --coqc`, then the two drivers. Proof compiler
processes have 150-second bounds; the 29-record assumption driver has a
600-second bound based on measured prior traversals. The full kernel root is
`OwnC.jet_secp_scalar_multiply_local`, using `--coqchk -silent -o` with a
600-second process bound and 65,520 KiB stack. New source edits require fresh
rebuilds/reports/kernel evidence, not a prior `.vo` or this receipt.

See `CONTINUATION.md` for registry integration and square. Preserve unrelated
dirty registry/range/SHA/field-negate work and Claude's reserved modules.
Signed atomic local commits only; never push.
