# Actual calculation-jet lifecycle pieces

This package composes the actual original Elements AST pieces for
`calculate_asset`, `calculate_explicit_token` and `calculate_confidential_token`.
It is proof support, not three complete public equivalence theorems yet.
The private sources are at `/private/tmp/jet-elements-calculation-lifecycle.AQFiRO`.

Recovery note (2026-10-18): that temporary directory and its basis have since
disappeared, and process handle 17504 is no longer available. The archived
`RUN.json` records successful compilation and complete reports only. The
kernel launch has no recovered terminal result and no `CHECKED.json`; do not
treat it as passed or reuse its missing objects. Preserve these exact historical
records. A new recovery run must freshly rebuild the source basis and extensions
and record its own source/object bindings and terminal result separately.

- `Entry`: the real four-local header and function-entry derivation.
- `Allocation`: shared fresh allocation, ownership and preservation facts.
- `Shape`: the actual statement tree, expression/call/copy proofs and the
  enclosing function composition rule (internal execution/store/free premises).
- `Read`: derives four real allocations, the 16-byte source copy, and the
  eight-word reader call from the initial Word256 frame. Proves the exact
  canonical input registers, updated local cursor, old-memory preservation,
  freshness, distinctness and retained ownership of all locals.
- `Writer`: derives the original static `writeHash` call and output cells,
  cursor, prefix, outside-load framing and permission preservation from a
  canonical register array and writable frame. No zero-output or fixed-cursor
  assumption is added; word-boundary crossings use the existing core writer.

The source-bound 196-module basis is `../elements-calculation-calls/`, including
its checked, byte-identical Elements/SHA proof-loading alias. No production C,
specification, API or generation setting changes. `verify.py EXTERNAL_DIRECTORY`
freshly compiles all five modules, checks all 32 theorem and 19 definition
reports against an exact per-result dependency profile, binds loaded local
sources/objects to that basis, and recursively checks the kernel. `CHECKED.json`
exists only after success; a launch/compile record is not kernel success.

Remaining: combine the input prefix with the canonical calculation helper call
(explicit libc/dispatch premises), derive the returned struct's byte copy and
register preservation, invoke the writer, free all four actual locals, and
discharge the internal composition rule from initial public frames. Only then
state the three concrete public jet contracts. This package adds zero accepted
coverage and does not assert that that end-to-end step is complete.
