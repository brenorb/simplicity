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

The immediate milestone is unrestricted initialized output words at the
currently proved single-word cursor positions, with preservation of the bits
outside the output slice. The app's existing goal record cannot be edited or
resumed through the available goal API; this file records the revised work plan.
The user's `jet-proof-review.patch` is an existing untracked review artifact
and must not be overwritten or included in proof commits.

## What is proved

The new public results are:

- `Coq/C/jet_increment8_spec.v:eval_increment8_matches_spec`
- `Coq/C/jet_one8_call.v:eval_one8_initial_matches_spec`

They construct complete executions of the actual generated Clight jet bodies
from initial loads and write permissions. They do not assume helper execution,
successful intermediate stores, or the desired output. Increment covers all
256 input values, including overflow, against the canonical primitive
Simplicity increment term (carry-in one plus input plus a zero word).
The earlier adder-with-one definition has been replaced with that canonical
composition. One uses `true >>> left_pad_low word1 word8`.

Both prove the decoded output, true return, destination cursor advancement,
and preservation of loads outside the two destination blocks. The regenerated
AST and all jet proof dependencies compiled successfully; the targeted build
finished with exit status 0 through `C/check_jet_assumptions.vo`.

These are **concrete-layout** theorems: one 64-bit word, zero-initialized
destination, initial output offset 9 (increment) or 8 (one), and input offset
56 (increment). They do not establish arbitrary frame positions, crossing
branches, arbitrary output initialization, or `add_8`.

See [the proof documentation](Coq/C/JET_PROOFS.md) for exact contracts,
dependency structure, assumptions, build instructions, and remaining scope.

## Important provenance correction

The original generated `jets.v` used removed handwritten headers. It has now
been regenerated from `Coq/C/jet_translation_unit.c`, which includes the real
`C/frame.c` and `C/jets.c`, using genuine Debian amd64 glibc headers.
The real `UINT8_MAX` constant has type `int`, not `unsigned int`.
The increment expression proof now follows that exact type.

This is explicitly an x86-64 Linux, little-endian, LP64, assertion-disabled
build (`NDEBUG` plus Simplicity's required `RECKLESS`). C11 static assertions
are still checked. No generated function body was edited manually.

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

## Remaining work beyond the concrete-layout results

1. Generalize output initialization and cursor positions, then crossing paths.
2. Extend `read8` to offset 48 and compose two calls for `add_8`.
3. Preserve the public initial-memory-only theorem interface; do not reintroduce
   assumed helper contracts or successful-store premises as final results.
4. If claiming uniqueness or a small-step theorem, prove the corresponding
   determinism/soundness result explicitly.
5. Keep all work local. Scope searches to this repository and known dependency
   paths; do not search unrelated personal folders.

The inherited execution assumptions are CompCert's classical/extensionality
and real-number decisions plus the external-semantics parameters in the Clight
relation. No new axioms, admits, or aborted proofs were introduced. The
increment output-denotation and monadic interpretation bridges are closed
under the global context.
