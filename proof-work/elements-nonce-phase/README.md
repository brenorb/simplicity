# Original nonce-processing C phase

`nonce_phase_exec` derives execution of the actual `nc_nonce` statement tree
in `elements_ge` for every optional nonce, from its encoded input and a live
SHA context. The `nc_nonce` body equality was independently checked against
the original `simplicity_nonce_hash` AST in `../elements-nonce-context/`.

The proof composes the actual tag reads and their temporary updates, the
explicit case's padding skip, the parity-selected `sha256_uchar` calls, the
32-byte `read8s`, and `sha256_uchars`. The resulting context has absorbed
exactly `nonce_hash_bytes`, already linked to the literal Simplicity program.
It preserves the precise nested overflow flag, adds one or 33 to the machine
counter, and proves cursor, permissions, validity and outside-local load
preservation. Absent nonce consumes only its tag bit; present nonce consumes
259 bits. The source frame is a private by-value copy, so the final public
contract must not require an incorrect fixed cursor advance in the absent case.

`Effects.v.source` provides reusable effect composition and frame/input/context
preservation. Undefined padding cells retain physical bit readability, not
merely an unconstrained logical value. `Calls` derives each actual statement
from the existing C helper contracts. `Prefix`, `Payload` and `Phase` compose
those contracts; they do not assume the desired calls execute.

This is **not yet the whole jet theorem**. Its initial live `ctx_abs`, writable
private arrays, input frame and local/global block-separation premises must be
derived from the outer function's allocation/initialization/context reader.
Both invalid-context and overflow paths, context output writing, function
return and freeing all locals still need final composition. The existing
explicit `memcpy_model` is retained. No field/curve or nonce-value restriction,
new axiom, production-target change, normal registration or accepted coverage
is introduced.
