# Complete original Elements nonce_hash jet

`Actual.nonce_hash_local_spec` proves execution of the actual
`jets_elements.f_simplicity_nonce_hash` in `elements_ge` against the literal
Simplicity `NonceContext.Spec.nonce_hash_spec`, interpreted in `optalg`.
It is an implementation-to-specification theorem, not only a byte-stream or
mathematical relationship between specifications.

The input is 1089 bits (830-bit context plus 259-bit optional confidential
nonce); the output is an 830-bit context. All nonce variants and arbitrary
valid frame positions, boundary crossings and pre-existing output bits are
covered. An invalid initial compression count returns false. A final count
overflow also returns false, as the option semantics requires. Successful
calls write the canonical encoding, preserve the preceding output bits and
advance the output cursor. All four actual locals are allocated and freed in
the original order; loads outside the permitted output ranges are preserved.
The source frame is copied by value. The private copy consumes one nonce bit
for absence, or 259 for presence; no false fixed-consumption claim is made.

The conditional premises are the existing explicit `memcpy_model`, the actual
Elements SHA dispatch and maximum-counter loads, and ordinary readable-input /
writable-output frame representations. No desired execution, result or
intermediate SHA state is assumed. Initial-memory/frame constructibility is
not yet part of this packet.

## Reuse and fidelity

- `Common` contains the contract, source-copy derivation, exact original
  entry/free-list adapters and small representation/counter/temporary lemmas.
- `Values` reuses the complete `ctx8_add_values` proof from
  `Coq/C/jet_sha_add_buffer_spec.v`, renaming only that theorem. This avoids
  recompiling or changing a frozen parent dependency tree.
- `Local` adapts the four-local context lifecycle of
  `Coq/elements-sha/C/jet_elements_annex_hash_jet.v`. Its entire annex middle
  is replaced by `NonceExec.Phase.nonce_phase_exec`, not asserted to be the
  same code. `nc_body_shape` checks the actual nonce body; the writer uses
  its real `_t'5` temporary.
- `Actual` exposes the original Elements environment and symbols. The private
  SHA proof overlay is the byte-identical original Elements AST, connected by
  the checked `elements_sha_program` / `elements_sha_genv` equalities. The
  production AST, implementation, canonical specification and API are unedited.
- The literal canonical-program review and option/byte bridge are inherited
  from `elements-nonce-context`; the manual source review is not claimed to
  be a formal Haskell translation theorem.

## Reproduction and verification scope

```sh
python3 -B proof-work/elements-nonce-local/verify.py compile EXTERNAL_DIRECTORY
python3 -B proof-work/elements-nonce-local/verify.py kernel EXTERNAL_DIRECTORY
```

Copy the four archived `.v.source` files to an otherwise empty external
directory as `Common.v`, `Values.v`, `Local.v` and `Actual.v`. The driver uses
the recorded parent trees, compiler and load paths. It freshly compiles all
four files, reports full types/definitions/assumptions, binds 260 local
imports to their forced-source/object provenance and checks seven inherited
external modules. Eleven results have exactly six closed proofs, two using
four inherited dependencies and three using the six inherited CompCert/VST
dependencies. `memcpy_model` remains an explicit premise, not a discharged
libc implementation fact.

`RUN.json` records compilation, not a completed recursive kernel audit.
`KERNEL-RUN.json`, when present, records a launch only. Only `CHECKED.json`
with successful `kernel` exit status establishes that recursive `coqchk`
finished for those exact inputs. Reuse the live process handle rather than
restarting a silent audit. The complete audit does not require the separate
phase audit to finish first: it recursively checks that dependency itself.

This packet is unregistered; accepted coverage added is zero. Normal
registration, inherited boundary review and remaining repository-wide jet
proofs are separate unfinished work.
