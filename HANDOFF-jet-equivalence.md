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
The newest `one_8` theorem supports arbitrary non-wrapping source/output
structure addresses, output edge addresses, and output cursors/word indices,
including crossings. It consumes `write_frame_at` and a readable aligned
16-byte source copy region, and proves the canonical primitive result.
Increment and add also have complete crossing-output equivalence theorems
for cursors 65..72: all eight ways their nine output bits span two words.
The carry-at-the-boundary case (cursor 65) is included.
The preceding frame theorems also cover two-word input alignment: read cursors 0..120
for increment and 0..112 for add, with independent output cursors 9..72. This includes
crossing reads, either operand crossing, and exact-boundary reads. Their input
frame edge is offset 16, with high/low words at offsets 8/0.
The newest input-layout theorems remove those input restrictions: source-frame
offsets, input edge addresses, and backing-word indices are arbitrary, subject
to explicit non-wrapping bounds and readable byte slices. Outputs still use
fixed bases and independent cursors 9..72.
All preserve the already-written prefix. The crossing theorem consumes
`write_frame` directly and constructs all stores from its permissions.
The user's `jet-proof-review.patch` is an existing untracked review artifact
and must not be overwritten or included in proof commits.

## What is proved

The new public results are:

- `Coq/C/jet_one8_layout.v:eval_one8_layout_matches_spec`
- `Coq/C/jet_increment8_input_layout.v:eval_increment8_input_layout_matches_spec`
- `Coq/C/jet_add8_input_layout.v:eval_add8_input_layout_matches_spec`
- `Coq/C/jet_increment8_frames.v:eval_increment8_frames_matches_spec`
- `Coq/C/jet_add8_frames.v:eval_add8_frames_matches_spec`
- `Coq/C/jet_add8_spec.v:eval_add8_cursors_matches_spec`
- `Coq/C/jet_add8_crossing.v:eval_add8_crossing_matches_spec`
- `Coq/C/jet_add8_two_words.v:eval_add8_two_words_matches_spec`
- `Coq/C/jet_increment8_cursors.v:eval_increment8_cursors_matches_spec`
- `Coq/C/jet_increment8_crossing.v:eval_increment8_crossing_matches_spec`
- `Coq/C/jet_increment8_two_words.v:eval_increment8_two_words_matches_spec`
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

The older input contracts use a **single-word layout**, with arbitrary unused
bits and independent read/write cursors. The newer `two_word_input` contract
supports a sequence of bytes within two initialized words; the reader proves
all three paths (high word, crossing, low word). The newest complete jet
theorems use `byte_input_at` to generalize input bases and word indices, with
a shared `output9` contract for output cursors 9..72, covering non-crossing and
crossing outputs. General output frame/base offsets, arbitrary output
backing-word indices, and output cursors beyond 72 remain unproved for
increment/add. `one_8` now supports those general output layouts.
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
After adding general crossing writes and both crossing jet theorems, the
targeted build and assumption audit passed again. Independent
`coqchk -silent C.jet_increment8_crossing C.jet_add8_crossing` also passed
(exit status 0). The crossing-byte interpretation and increment's split-value
bridge are closed under the global context.
After integrating two-word inputs, the targeted build and assumption audit
passed again. Independent
`coqchk -silent C.jet_increment8_two_words C.jet_add8_two_words` passed
(exit status 0). The crossing-read value bridge is closed under the global context.
After unifying both output paths, the full targeted build and assumption audit
passed again. Independent
`coqchk -silent C.jet_increment8_frames C.jet_add8_frames` passed (exit status 0).
The new frame theorems inherit the same assumptions as the preceding executions;
the carry/byte bit-slice lemmas introduce no axioms.
After generalizing input addresses in both full jet theorems, the targeted
build and assumption audit passed again. Independent
`coqchk -silent C.jet_increment8_input_layout C.jet_add8_input_layout` passed
(exit status 0), with the same inherited execution assumptions.
After adding the total arbitrary-address byte writer and complete general-layout
one jet, the targeted build and assumption audit passed again. Independent
`coqchk -silent C.jet_write8_layout_total C.jet_one8_layout` passed (exit status 0).
The total bit writer and carry/byte composition then passed the targeted build
and assumption audit, and independent `coqchk -silent C.jet_carry_byte_layout`
passed (exit status 0). The bit-value and prefix lemmas are closed under the
global context; execution inherits the same CompCert assumptions as before.

## Remaining work beyond the concrete-layout results

1. Generalize physical frame/backing-word base offsets and arbitrary
   backing-word indices. Crossing input/output paths are individually proved
   and composed with non-crossing paths in the newest unified frame theorems.
   The destination frame struct still starts at block offset 0, with output
   edge 0. Removing these output restrictions is the next milestone. The newest
   public `eval_increment8_input_layout_matches_spec` and
   `eval_add8_input_layout_matches_spec` remove the input restrictions: arbitrary
   source-frame offsets, input edge addresses and word indices are supported.
   The generalized reader is now checked: `eval_read8_layout` covers arbitrary
   frame structure offsets, edge addresses, cursor word indices, and crossings.
   Its premises are initial memory facts; it constructs both cursor stores
   where needed and preserves all loads outside the cursor field. It is now
   composed into both complete jets through `byte_input_at` / `eval_read8_byte_at`.
   The total byte writer and full one jet now support general output layouts;
   composing the general writers into increment/add remains to be done.
   Checked raw writer execution now exists in `jet_writeBit_layout.v` and
   `jet_write8_layout.v`: both bit values and both byte paths allow arbitrary
   output structure offsets, edge addresses and word indices. The shared
   `jet_write_layout.v` proves address/cursor arithmetic. These raw lemmas still
   take successful stores. `eval_write8_layout` now constructs those stores
   from `write_frame_at`, proves `byte_output_at` and `write_prefix_at`, and
   preserves loads outside the modified cursor/word ranges. `eval_writeBit_layout`
   now does the same for a bit. `eval_carry_byte_layout` constructs both actual
   helper calls from a nine-bit `write_frame_at` and proves `carry_byte_output_at`,
   written-prefix preservation, final cursor, precise load preservation,
   and permission/valid-block preservation. The full one jet
   uses it via `eval_one8_layout_composes`, including nonzero destination and
   source offsets. Integration of the carry/byte result into the full
   increment/add function boundaries remains pending: their entry/body proofs
   still fix the destination pointer at block offset 0. Generalize that pointer
   while reusing their actual scalar arithmetic and canonical value bridges.
   The raw writers' targeted build/assumption audit and independent
   `coqchk -silent C.jet_writeBit_layout C.jet_write8_layout` passed.
2. Extend to larger widths, reusing the generalized frame infrastructure.
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
Subsequent commits: `b9f3a23`/`938eaee` (add execution/specification),
`3fc25f9` (arbitrary-byte crossings), `4128275` (second-word carry writes),
and `0689840` (all eight carry/byte splits).
Then `8306e5f` completed the crossing-output jet proofs, `669dc6b` proved
crossing reads, and `36e6ba9` introduced total two-word reads and input contracts.

Completed add implementation notes: the generated add jet reads twice, binds `_x` and
`_y`, writes carry `255U - y < x`, then the truncated sum. Its local-frame
copy/allocation/free pattern matches increment. `jet_add8_call.v` constructs
both local cursor stores from initial permissions. `jet_add8_word.v` proves
the symbolic bridge; `jet_add8_spec.v` exposes the initial-memory-only theorem. Arithmetic
promotion still makes the comparison unsigned even though real glibc's
`UINT8_MAX` literal has type `int`. For Word8, `Word.adder` unfolds to the
same `false &&& iden >>> full_add` composition as Haskell's `add word8`.

Crossing implementation notes: `jet_write8_crossing_general.v` proves the
actual writer for arbitrary payloads, keeping the C signed-shift/cast sequence
in `crossing_high`. `jet_crossing_byte.v` interprets it symbolically using
testbit lemmas; no payload enumeration is used. `jet_writeBit_high.v` covers
cursors 65..128. `jet_write8_split.v` handles byte cursors 64..71, including
the exact boundary. `jet_carry_byte_crossing.v` composes both actual calls
for all eight nine-bit splits and proves permission preservation, which the
outer jet proofs use to free their local source-frame copies.

Input implementation notes: `jet_read8_crossing.v` proves the generated
crossing branch, and `jet_read8_crossing_word.v` relates its casts/shifts to
`crossing_byte` without enumerating payloads. `jet_read8_two_positions.v`
handles non-crossing reads in either word. `jet_read8_two_words.v` constructs
all cursor stores and exposes a total read contract for cursors 0..120,
preserving other-block loads, permissions, and valid blocks.
`jet_two_word_input.v` represents a byte sequence and supplies single/pair
elimination lemmas. The two-word increment/add proofs use that contract directly;
they do not assume read executions or intermediate-store success.

Unified output notes: `jet_carry_byte_position.v` constructs non-crossing
carry/byte calls for arbitrary payloads. `jet_output9.v` combines it with
the crossing writer under `write_frame`, and defines `output9` and
`output9_prefix` independently of which output path executes.
Its preservation lemmas let the public frame theorems transport these contracts
across source preparation and local-frame freeing without repeating each path.
The older crossing-only and single-word theorems remain checked regressions.

Arbitrary-address reader notes: `jet_frame_layout.v` proves field accesses for
nonzero structure offsets; `jet_read8_layout.v` executes both generated branches
at arbitrary word indices, with explicit non-wrapping address bounds.
`jet_read8_layout_total.v:eval_read8_layout` constructs the stores and preserves
loads outside the eight-byte cursor field, including in the same memory block.
`jet_frame_copy_layout.v` preserves pointer fragments and cursor loads when
copying a source frame at a nonzero offset to the jet's fresh local frame.
The reader's full targeted build/assumption audit and independent
`coqchk -silent C.jet_read8_layout_total` passed (exit status 0).

Arbitrary-output composition notes: `write_frame_at_after_bit` transports the
remaining writable cells after a bit store, including initialized-word loads.
`write_layout_previous_inside` / `write_layout_previous_boundary` identify the
next byte's word and in-word position. `eval_carry_byte_layout` uses the byte
writer's prefix/range postconditions to preserve the carry and original prefix,
without enumerating cursor values. `carry_byte_output_at` observes the carry
at `(cursor-1) mod 64` and the following byte via `byte_output_at` at `cursor-1`.
All current modules compile; no unfinished proof is left in the tree.

Known check times: a production AST change triggers the older `jet_exec.v`
(about four minutes) and `jet_write8.v` (about three minutes). The new symbolic
cursor/crossing modules compile in under a second each. Avoid modifying sources
under a running compiler or launching duplicate builds; no proof experiment
is currently left failing.
