# Handoff: C jet equivalence to Simplicity

Updated 2026-09-22. All work is local on `feat/jet-equivalence`; nothing has
been pushed. The user's latest instruction removes the requirement to ask an
Astra Medium subagent for guidance. Continue using the Coq Proof Engineering
skill and frequent, atomic local commits.

## Revised active goal (user-approved continuation)

Strengthen the implementation-to-Simplicity results, preserving the existing
checked theorems as regression tests. First introduce reusable frame/bit-slice
contracts and remove zero-output and exact-input-padding restrictions for
`one_8` and `increment_8`. Then generalize valid cursor positions and crossing
paths, cover the intended assertion configuration, and extend to `add_8` and
larger widths. Improve symbolic word lemmas and reusable memory contracts as
needed; never replace actual helper execution with assumed behavior.

The app goal is active again. Its old objective cannot be edited through the
available API; this file records the revised plan and supersedes the obsolete
instruction in that record to consult Astra Medium.

Completed: unrestricted initialized output words, arbitrary unused input bits,
independent in-word input/output cursors for increment (read 0..56, write 9..64),
and one at output cursors 8..64 plus all seven two-word splits (65..71).
Also completed: all-input `add_8` equivalence at independent non-crossing
read cursors 0..48 and write cursors 9..64, with arbitrary input padding and
initialized output contents. Its value bridge is symbolic, not exhaustive.
All preserve the already-written prefix. The crossing theorem consumes
`write_frame` directly and constructs all stores from its permissions.
The user's `jet-proof-review.patch` is an existing untracked review artifact
and must not be overwritten or included in proof commits.

## What is proved

The new public results are:

- `Coq/C/jet_add8_spec.v:eval_add8_cursors_matches_spec`
- `Coq/C/jet_increment8_cursors.v:eval_increment8_cursors_matches_spec`
- `Coq/C/jet_one8_position.v:eval_one8_position_matches_spec`
- `Coq/C/jet_one8_crossing.v:eval_one8_crossing_matches_spec`

The original fixed-cursor/zero-output results remain compiled as regression
tests. The generalized byte writer also covers arbitrary payload bytes at
every non-crossing cursor (`jet_write8_position.v:eval_write8_position`).
`jet_read8_position.v:eval_read8_position` covers read cursors 0..56, including
the 48/56 pair needed for `add_8`. `jet_LSBkeep_width.v` and
`jet_LSBclear_width.v` prove actual mask-helper calls for widths 1..64.

They construct complete executions of the actual generated Clight jet bodies
from initial loads and write permissions. They do not assume helper execution,
successful intermediate stores, or the desired output. Increment covers all
256 input values, including overflow, against the canonical primitive
Simplicity increment term (carry-in one plus input plus a zero word).
The earlier adder-with-one definition has been replaced with that canonical
composition. One uses `true >>> left_pad_low word1 word8`.

All prove the decoded output, true return, destination cursor advancement,
and preservation of loads outside the two destination blocks. The regenerated
AST and all jet proof dependencies compiled successfully; the targeted build
finished with exit status 0 through `C/check_jet_assumptions.vo`.

The increment theorem still uses a **single-word layout**, now with arbitrary
initialized destination and independent read/write cursors. One also covers
two-word crossings at the first boundary. They do not establish general
frame/base offsets or increment/add's crossing branches.
For a nonzero final cursor, preserve the already-written prefix, not the
unused low bits: the real C writer clears those low bits.

See [the proof documentation](Coq/C/JET_PROOFS.md) for exact contracts,
dependency structure, assumptions, build instructions, and remaining scope.

## Important provenance correction

The original generated `jets.v` used removed handwritten headers. It has now
been regenerated from `Coq/C/jet_translation_unit.c`, which includes the real
`C/frame.c` and `C/jets.c`, using genuine Debian amd64 glibc headers.
The real `UINT8_MAX` constant has type `int`, not `unsigned int`.
The increment expression proof now follows that exact type.

The current generated artifact is x86-64 Linux, little-endian, LP64, in the
library-recommended `PRODUCTION` mode. Ordinary assertions and C11 static
assertions are enabled; `NDEBUG` and `RECKLESS` are absent. Debug assertions
are behind the actual generated false guard, which the writeBit proof executes.
No generated function body was edited manually. The older commits retain the
previous NDEBUG/RECKLESS proofs; do not confuse their configuration with HEAD.

Global helper blocks now come from `jet_symbol_block` plus checked lookup
lemmas, not hardcoded 71/72/75/83/87 positions. Production added assertion
strings/globals and moved these blocks, so this refactor is essential.

`regenerate-jets.sh` defaults to production and supports explicit-output
`JET_ASSERTIONS=debug` / `reckless`. Fully debug-enabled generation and Coq
AST compilation were tested in `/tmp/simplicity-assertion-audit.QlmC95`, but
debug-mode jet execution remains unproved. `check-jets-generation.sh` compares
regenerated output without changing the committed AST.

The regeneration script was run twice and its output compared byte-for-byte
with the committed artifact. The pinned Debian package and checksum are in
`JET_PROOFS.md`.

## Reproduce checks

Compatible local tools:

- opam root: `/Users/brenorb/.opam-simplicity-root`, switch `simplicity`
- Coq 8.17.1
- CompCert 3.14: `/tmp/simplicity-compcert`
- VST 2.14 with SHA libraries: `/tmp/simplicity-vst`
- Linux header sysroot: `/tmp/simplicity-linux-sysroot.Nb5jW9`

From the repository root:

```sh
env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  COMPCERT=/tmp/simplicity-compcert VST=/tmp/simplicity-vst \
  opam exec --switch=simplicity -- bash Coq/build-jets.sh -j2
```

The targeted makefile builds `C/check_jet_assumptions.vo`. Proof imports now
use `C.jets`; the obsolete top-level `/tmp/jets.vo` is not needed. Do not
recursively map all of `/tmp` into Coq's empty namespace. Do not claim that
unrelated secp/divsteps or whole-project builds pass.

Latest verification: all changed jet modules rebuilt successfully against the
regenerated `C.jets`; `Print Assumptions` reports only the inherited assumptions
listed below. The regeneration script's output matches `Coq/C/jets.v` exactly.
The proof sources contain no admits, new axioms, aborted proofs, or unchecked
cast escapes. No failing or uncompiled proof experiment remains in the tree.
After the production migration, the complete targeted build and assumption
audit passed again (exit status 0). A separate
`coqchk -silent C.jet_increment8_cursors C.jet_one8_crossing C.jet_one8_position`
run with the same load paths also completed successfully (exit status 0).
AST regeneration checked byte-for-byte, script syntax checks passed, and invalid
assertion modes/implicit alternate-mode overwrites were rejected as intended.
After adding `add_8`, the full targeted build and assumption audit passed
again, as did `coqchk -silent C.jet_add8_spec` (all exit status 0).
The symbolic add value bridge and its monadic interpretation are closed
under the global context.

## Remaining work beyond the concrete-layout results

1. Extend the crossing writer from byte value one to arbitrary bytes, then
   support increment's carry-bit write into the high word and crossing reads.
   Generalize physical frame/backing-word base offsets as a separate step.
2. Extend increment/add beyond single-word reads/writes, then to larger widths.
   `add_8` now uses `Word.adder` as its canonical primitive specification,
   with `Word.adder_correct` and `toZ` injectivity for a symbolic value bridge.
   Reuse those arithmetic lemmas rather than enumerating byte pairs.
3. Preserve the public initial-memory-only theorem interface; do not reintroduce
   assumed helper contracts or successful-store premises as final results.
   Fully debug-enabled execution would also require proving the live writeBit
   assertion path, not reusing the production false-guard lemma.
4. If claiming uniqueness or a small-step theorem, prove the corresponding
   determinism/soundness result explicitly.
5. Keep all work local. Scope searches to this repository and known dependency
   paths; do not search unrelated personal folders.

Proof-engineering notes for this continuation: `Archi.ptr64` is globally opaque
in CompCert, so `jet_write8_position.v` makes it locally transparent rather than
computing symbolic memory goals. Closed `UWORD_BIT` evaluation is isolated in
`eval_generated_uword_bits`. Casted integer constants must be normalized before
rewriting symbolic shift bounds. New cursor proofs compile in under a second;
do not replay the older multi-minute helper proofs for local tactic debugging.

The inherited execution assumptions are CompCert's classical/extensionality
and real-number decisions plus the external-semantics parameters in the Clight
relation. No new axioms, admits, or aborted proofs were introduced. The
increment output-denotation and monadic interpretation bridges are closed
under the global context.

Recent local proof commits: `ae8f263` (carry cursors), `612d7fc` (increment
output cursors), `e0be9cf` (crossing execution), `3639174` (crossing one theorem),
`f10be65` (independent increment cursors), and `c46668f` (production assertions,
checked dynamic symbol blocks, and reproducible AST checking).

Completed add implementation notes: the generated add jet reads twice, binds `_x` and
`_y`, writes carry `255U - y < x`, then the truncated sum. Its local-frame
copy/allocation/free pattern matches increment. `jet_add8_call.v` constructs
both local cursor stores from initial permissions. `jet_add8_word.v` proves
the symbolic bridge; `jet_add8_spec.v` exposes the initial-memory-only theorem. Arithmetic
promotion still makes the comparison unsigned even though real glibc's
`UINT8_MAX` literal has type `int`. For Word8, `Word.adder` unfolds to the
same `false &&& iden >>> full_add` composition as Haskell's `add word8`.

Known check times: a production AST change triggers the older `jet_exec.v`
(about four minutes) and `jet_write8.v` (about three minutes). The new symbolic
cursor/crossing modules compile in under a second each. Avoid modifying sources
under a running compiler or launching duplicate builds; no proof experiment
is currently left failing.
