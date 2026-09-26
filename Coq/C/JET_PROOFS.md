# C jet implementation-to-Simplicity proofs

## Public results and exact scope

`jet_one8_layout.v:eval_one8_layout_matches_spec` proves the complete `one_8`
call for arbitrary non-wrapping source-frame and output-frame addresses, output
edge addresses, and output cursors/word indices. Its `write_frame_at` contract
constructs all stores from initial permissions; both byte paths are covered.
The unused source frame only needs an aligned readable 16-byte copy region.
The result equals the canonical primitive `one8_spec`, the final frame cursor
is `cursor-8`, and the already-written prefix is preserved. Loads outside the
modified cursor/word ranges are preserved even within the destination blocks.

`jet_one_wide_layout.v:eval_one_wide_layout_matches_spec` extends the complete
one-jet result to **one_16, one_32 and one_64**, selected by `W16`, `W32` and
`W64`. It uses the actual generated function bodies and the canonical
`true >>> left_pad_low word1 wordN` primitive Simplicity programs. It supports
arbitrary non-wrapping output cursors and crossings, initialized arbitrary
output contents, and arbitrary aligned source-frame copy addresses. The
shared `eval_write_wide_layout` proves actual 16/32/64-bit writer execution
for every unsigned-long payload, with width-parametric projection/prefix lemmas.
All successful stores are derived from `write_frame_at`; none are assumed by
the public complete-jet theorem. `wide_output_at` observes the extracted n-bit
payload at its actual word locations and decodes it to the Simplicity word.

`jet_increment8_layout.v:eval_increment8_layout_matches_spec` and
`jet_add8_layout.v:eval_add8_layout_matches_spec` now prove the complete
increment/add calls with arbitrary non-wrapping input **and output** frame
addresses, edge addresses, word indices, and independent cursor positions.
The initial contracts are `byte_input_at` and `write_frame_at`; there are no
assumed intermediate stores or helper executions. `carry_byte_output_at`
relates the actual carry and byte locations to the canonical primitive
Simplicity result. The final destination frame advances by nine bits, the
written prefix is preserved, and loads outside the modified ranges are
preserved even inside the destination blocks.

The 64-bit arithmetic jets are covered as well. `jet_read64_layout_exec.v`,
`jet_read64_layout_total.v`, and `jet_read64_input_word_total.v` prove the
generated `read64` across aligned and crossing layouts, derive its stores from
initial permissions, and relate its `Vlong` result to the exact `Word 6` input.
`jet_increment64_layout.v:eval_increment64_layout_matches_spec` proves the
complete `increment_64` call. `jet_add64_layout.v:eval_add64_layout_matches_spec`
proves the complete `add_64` call for two consecutive `Word 6` values. Both
public theorems accept arbitrary valid non-wrapping input/output cursors,
including crossings, arbitrary unrepresented input bits, and arbitrary
initialized output contents; all helper calls and intermediate stores are
derived from the initial frame contracts.

The arithmetic bridges are `jet_increment64_wide_word.v` and
`jet_add64_wide_word.v`. The latter follows the actual C carry test
`(UINT64_MAX - y) < x` and proves both its equivalence to the Simplicity carry
and the modular 64-bit payload result in the machine-wrap case. The proof
reuses the shared reader, wide-writer, carry/wide-output, frame-copy, and
lifecycle contracts rather than enumerating 64-bit inputs.

The preceding input-layout results are
`jet_increment8_input_layout.v:eval_increment8_input_layout_matches_spec` and
`jet_add8_input_layout.v:eval_add8_input_layout_matches_spec`. Their
`byte_input_at` contract permits arbitrary non-wrapping source-frame and input
edge addresses, arbitrary input word indices, and every input alignment,
including crossings. Only the represented byte slices are constrained.
They retain output cursors 9..72 with the output frame at block offset 0 and
output edge 0. These are full calls of the generated C jets, including the
by-value source-frame copy, allocation, stores, return and freeing.

The preceding unified results are
`jet_increment8_frames.v:eval_increment8_frames_matches_spec` and
`jet_add8_frames.v:eval_add8_frames_matches_spec`. They support every input
alignment within two backing words (read cursors 0..120 and 0..112 respectively)
and independent output cursors 9..72. Their initial output contract is
`write_frame`; the final `output9` contract decodes either the non-crossing
or crossing nine-bit result and equals the canonical Simplicity specification.
`output9_prefix` preserves the already-written prefix of the touched word.
All helper executions, allocations, frame copies, stores, and freeing are proved.

`jet_add8_spec.v:eval_add8_cursors_matches_spec` proves complete execution of
the generated `f_simplicity_add_8` against the canonical primitive
`Word.adder` (`false &&& iden >>> full_add word8`). It covers every pair of
byte inputs, including carry, at read cursors 0..48 and independent output
cursors 9..64. Both reads fit in one word; unrelated input bits and the initial
output word are arbitrary. The arithmetic bridge uses `Word.adder_correct`
and injectivity of the word encoding, with no input-pair enumeration.
`jet_add8_crossing.v:eval_add8_crossing_matches_spec` additionally covers
all eight nine-bit output crossings (cursors 65..72). Its initial output
contract is `write_frame`, and the two-word decoder is `decode_carry_crossing`.

`jet_increment8_cursors.v:eval_increment8_cursors_matches_spec` constructs a complete
`ClightBigstep.Clight2.eval_funcall` of the generated
`f_simplicity_increment_8`, returning true with an empty trace. For every
`x : Word8`, its nine decoded output bits equal the functional evaluation of
the canonical Simplicity increment term. The term is the composition
`true &&& iden >>> full_increment word8`, where `full_increment` pairs the
input carry with the input word and a zero word before `full_add`.
This follows `Haskell/Core/Simplicity/Programs/Arith.hs`, not a replacement
integer addition specification.
`jet_increment8_crossing.v:eval_increment8_crossing_matches_spec` extends
this to output cursors 65..72 with the same initial `write_frame` contract.
Both increment/add crossing proofs include cursor 65, where only the carry
goes in the high word and the byte begins exactly at the next-word boundary.

`jet_increment8_two_words.v:eval_increment8_two_words_matches_spec` and
`jet_add8_two_words.v:eval_add8_two_words_matches_spec` additionally support
all input alignments within two initialized backing words. Increment permits
read cursors 0..120; add permits 0..112, covering either operand crossing and
exact-boundary reads. These theorems currently use output cursors 65..72.
Their shared `two_word_input` predicate describes a sequence of byte values
through bit slices; it assumes no execution or successful intermediate store.

`jet_one8_position.v:eval_one8_position_matches_spec` does the same for
`f_simplicity_one_8` and `true >>> left_pad_low word1 word8`, at any output
cursor from 8 through 64. It decodes the byte at bits `[cursor-8, cursor)`.
`jet_one8_crossing.v:eval_one8_crossing_matches_spec` additionally covers all
seven byte-crossing splits: output cursors 65 through 71, with backing words
at offsets 8 and 0. Its initial contract is the reusable `write_frame`
predicate, not a list of assumed successful stores. `crossing_byte` decodes
the high word's low `k` bits followed by the low word's high `8-k` bits.

The previous fixed-cursor and zero-initialized theorems remain checked
corollaries/regression tests.

These results prove the final output cursor (`cursor-9` for increment/add,
`cursor-8` for one) and preserve loads in
initially valid blocks other than the destination frame and output word.
Their premises contain **only initial memory facts and write permissions**.
Allocation, by-value source-frame copy, helper executions, stores, return
conversion, and deallocation are all proved. In particular, no successful
execution or successful intermediate store is assumed.

The general-layout results retain these explicit representation/target conditions;
the older specializations have additional restrictions described below:

- The target is x86-64, little-endian, LP64, using glibc integer typedefs.
- A frame is 16 bytes: pointer at offset 0, cursor at offset 8.
  The newest layout theorems permit both frame structures to begin at arbitrary
  aligned non-wrapping byte offsets, with these field offsets relative to the base.
- In the earlier single-word results, increment's source frame points one word past its input and has any cursor
  from 0 through 56. The eight bits beginning at that cursor encode the input
  `Word8`; every other input bit is arbitrary. Input and output cursors vary
  independently. The generalized reader includes cursor 48, needed before
  the second read at cursor 56 in a two-operand byte jet.
  Add's source frame has the same base layout and cursor 0..48; its two
  consecutive byte slices encode the input pair.
  The newer two-word source contracts instead use edge offset 16 and backing
  words at offsets 8 and 0. Only the represented bytes are constrained;
  all other bits are arbitrary.
  The newest `byte_input_at` contract removes the two-word/fixed-edge restriction;
  each read's word address is `edge - 8 * (1 + cursor / 64)` and a crossing
  reads the preceding word as well. Bounds rule out pointer and cursor wrapping.
- In the earlier specialized results, the output frame points to an initialized but otherwise arbitrary word
  and has any cursor in `[9,64]` for increment/add, or `[8,64]` for the single-word
  one theorem. The crossing one theorem uses two initialized words and a
  cursor in `[65,71]`.
  The crossing increment/add theorems use two initialized words at offsets
  8 and 0 and a cursor in `[65,72]`, preserving the high word's written prefix.
  The newest `write_frame_at` theorems remove fixed output bases and word indices
  and the cursor-72 ceiling. They require enough remaining cells (8 for one,
  9 for increment/add), a representable cursor, nonnegative edge, non-wrapping
  accessed addresses, initialized words and the stated write permissions.
  The output word and output frame are distinct blocks and writable in the
  stated locations. Both preserve all bits at or above the initial cursor
  (the already-written prefix), including the high word's prefix on crossings.
  C's writer may clear unused bits below the output slice; their preservation
  is intentionally not required.
- One's unused source frame must still be readable for its 16-byte C copy.
- The caller's environment argument is `Vundef`; none of these jets uses it.
- The generated artifact uses the library-recommended `PRODUCTION` mode:
  ordinary assertions remain enabled (`NDEBUG` and `RECKLESS` are not set),
  while debug assertions have a false guard. The writeBit proof executes that
  generated guard; it does not assume assertions succeed. Static assertions
  remain enabled and checked by clightgen.

The output frame and backing words must still be in distinct CompCert blocks;
same-block disjoint frame/backing regions are not covered. Other target ABIs,
fully debug-enabled execution (without `PRODUCTION`), and increment/add jets
wider than 64 bits are not established by these public theorems.
No binary-level linking or native ARM execution
claim is made. The results are constructive terminating Clight executions,
not separate universal determinism/small-step theorems.

## Proof organization

- `jet_write_layout.v`, `jet_writeBit_layout.v`, `jet_write8_layout.v`:
  generated writer executions at arbitrary output structure/edge addresses
  and word indices, including crossings. These raw execution lemmas still
  take successful stores; they are not yet generalized public jet theorems.
- `jet_output_layout.v`, `jet_write8_layout_total.v`: writable-frame contracts
  and a total byte-writer theorem for arbitrary addresses and word indices.
  The theorem constructs stores, decodes the byte, and proves precise memory
  preservation. `jet_one8_layout_exec.v` and `jet_one8_layout.v` compose it into
  the complete generated one jet, including source copy, allocation and freeing.
- `jet_writeBit_layout_total.v`, `jet_output_layout_step.v`,
  `jet_carry_byte_layout.v`: total arbitrary-address bit writes, writable-frame
  advancement, and carry/byte helper composition. `carry_byte_output_at` observes
  the carry bit and following byte at their actual frame positions. The proof
  covers the carry-at-boundary case, preserves the prefix and precise memory
  ranges, and derives all stores from initial permissions.
- `jet_arith8_layout_exec.v`: shared function entry, source-frame copy and
  writer-call rules, plus scalar expression evaluation independent of frame
  addresses. `jet_increment8_layout_exec.v` and `jet_add8_layout_exec.v` compose
  the actual generated calls; `jet_increment8_layout.v` and `jet_add8_layout.v`
  discharge their memory/execution premises and prove the canonical specifications.
- `jet_word_slice.v`, `jet_wide.v`, `jet_write_wide_layout.v`,
  `jet_output_slice.v`, `jet_write_wide_layout_total.v`: symbolic bit algebra,
  checked generated-function selection, and total arbitrary-layout 16/32/64-bit
  writers. The unsigned-long shifts are proved directly, without reusing the
  byte writer's different integer-promotion semantics.
- `jet_wide_spec.v`, `jet_one_wide_layout_exec.v`, `jet_one_wide_layout.v`:
  canonical wider one specifications and complete C-call equivalence.
- `jet_frame_layout.v`, `jet_read8_layout.v`, `jet_read8_layout_total.v`:
  frame-field accesses at arbitrary non-wrapping structure addresses and a
  total byte reader for arbitrary backing-word indices, including crossings.
  The reader constructs stores from initial permissions and preserves loads
  outside the cursor field, including other locations in the same block.
  `jet_input_layout.v` exposes byte-sequence input contracts and connects each
  actual read to a represented Simplicity `Word8`. `jet_frame_copy_layout.v`
  proves copying a source frame at a nonzero offset preserves its fields.
  Both are composed into the newest public input-layout jet theorems.
- `jet_input_layout.v` also defines algorithm-independent, MSB-first logical
  input bit/word predicates with append decomposition and load-preservation
  lemmas. `jet_read16_layout_exec.v:eval_read16_layout_non_crossing` proves
  actual W16 reader execution for arbitrary non-wrapping frame/edge addresses
  and cursors with `cursor mod 64 <= 48`. It still assumes the successful
  final cursor store. `eval_read16_layout_crossing` covers every crossing
  remainder (`48 < cursor mod 64 < 64`) at arbitrary non-wrapping addresses
  and word indices. It assumes two successful cursor stores, but derives the
  intervening low-word load from the initial load and block separation. The
  fixed-cursor zero/56 kernels remain regression results.
  These are checked execution lemmas, not yet a public reader contract or
  complete increment/add equivalence for W16. In particular, the logical
  `frame_input_word_at` predicate still needs to be connected to the returned
  integer, with an exact unsigned-value equality and a representable final
  cursor; decoding modulo 65536 alone is insufficient for carry arithmetic.
- `jet_frame_spec.v`: reusable bit/cursor/address predicates and the concrete
  single-word input/output contracts used by the public theorems.
  `jet_input_position.v` adds arbitrary in-word input slices. `write_frame`
  is consumed directly by the two-word one theorem; it is not yet an
  all-layout execution contract for either jet.
- `jet_word_bits.v`, `jet_word_decode.v`, `jet_word_position.v`: symbolic
  bit-slice replacement, decoding, and prefix preservation (no enumeration of
  old output contents or input padding).
- `jet_frame_arith.v`, `jet_frame_constants.v`, `jet_LSBclear_width.v`,
  `jet_write8_position.v`: bounded cursor arithmetic, one-time evaluation of
  the generated word-width expression, and actual helper execution at every
  non-crossing byte cursor. `eval_write8_position` discharges all helper-call
  premises; the outer jet theorem also constructs the stores from permissions.
- `jet_frame_copy.v`: copying raw `memval` bytes preserves frame pointer and
  cursor loads, including pointer fragments.
- `jet_frame_access.v`, `jet_LSBkeep_width.v`: offset-aware accesses and
  variable-width calls to the actual generated mask helper.
- `jet_crossing_arith.v`, `jet_write8_crossing.v`, `jet_crossing_word.v`:
  actual crossing execution for byte value one and its two-word interpretation.
  The seven-way split only computes bounded scalar layout/shift facts; memories
  and prior word contents remain symbolic.
- `jet_write8_crossing_general.v`, `jet_crossing_byte.v`,
  `jet_write8_crossing_frame.v`: arbitrary-byte crossing execution,
  symbolic two-word decoding/prefix preservation, and a writable-frame
  contract that constructs all stores and preserves permissions.
- `jet_writeBit_high.v`, `jet_crossing_frame.v`, `jet_write8_split.v`,
  `jet_carry_byte_crossing.v`: second-word carry writes, frame construction,
  exact-boundary byte writes, and composition across all eight nine-bit splits.
- `jet_carry_byte_position.v`, `jet_output9.v`: non-crossing composition and
  a shared writable-frame/output-value/prefix contract for output cursors 9..72.
  Frame/output preservation lemmas connect this contract to source preparation
  and local-frame freeing.
- `jet_read8_position.v`, `jet_writeBit_position.v`: actual helper execution
  at all in-word read and carry-bit cursors.
- `jet_read8_crossing.v`, `jet_read8_crossing_word.v`: actual two-word
  crossing reads and a symbolic proof that their result is the specified byte slice.
- `jet_read8_two_positions.v`, `jet_read8_two_words.v`, `jet_two_word_input.v`:
  high/low-word read paths, a total byte reader for all positions 0..120, and
  byte-sequence input contracts. The total reader constructs all stores and
  preserves permissions, valid blocks, and other-block loads.
- `jet_increment8_position_*.v`, `jet_increment8_cursors.v`: composition,
  memory construction, and public equivalence with independent cursors.
- `jet_add8.v`, `jet_add8_update.v`, `jet_add8_exec.v`, `jet_add8_call.v`:
  actual two-read/add/carry/write body, helper executions, and construction of
  the complete call from initial loads and permissions.
- `jet_add8_word.v`, `jet_add8_spec.v`: symbolic byte arithmetic, output-slice
  interpretation, prefix preservation, primitive specification parametricity,
  and the public all-input-pairs equivalence theorem.
- `jet_exec.v`, `jet_one8.v`, `jet_read8.v`, `jet_write8.v`, `jet_writeBit.v`:
  actual generated helper bodies, memory accesses, calls, and function entry.
  Helper blocks are now resolved with `jet_symbol_block`, with kernel-checked
  symbol/function lookup lemmas; no proof assumes numeric global-list positions.
- `jet_increment8.v`: exact arithmetic expressions, casts, and statement tree.
- `jet_increment8_exec.v`: threads the actual three helper calls and derives
  their intervening loads from CompCert store-preservation lemmas.
- `jet_increment8_call.v`: constructs all intermediate memories from initial
  permissions and closes the complete function boundary, including arbitrary
  initial backing words via `eval_increment8_concrete_word`.
- `jet_writeBit_general.v`, `jet_increment8_updates.v`,
  `jet_increment8_general_exec.v`, `jet_increment8_word.v`: carry-bit and byte
  updates, composition, and the bridge allowing arbitrary input padding and
  output contents.
- `jet_spec.v`: canonical primitive Simplicity terms and parametricity.
- `jet_increment8_cursors.v`, `jet_one8_position.v`, `jet_one8_crossing.v`:
  earlier position-specific C-to-Simplicity results. Earlier modules retain the
  fixed-layout special cases.
- `jet_increment8_crossing.v`, `jet_add8_crossing.v`: full jet equivalence
  for crossing outputs, with actual reads, frame copies, allocation and freeing.
- `jet_increment8_two_words.v`, `jet_add8_two_words.v`: full jet equivalence
  combining arbitrary two-word input alignment with crossing output alignment.
- `jet_increment8_frames.v`, `jet_add8_frames.v`: unified full jet equivalence
  combining the same inputs with both output paths, without assumed helper executions.
- `jet_increment8_input_layout.v`, `jet_add8_input_layout.v`: full equivalence
  with arbitrary input structure/edge addresses and word indices, retaining
  output cursors 9..72 and fixed output bases.

The increment value bridge exhausts the eight binary sum constructors (256
inputs) using kernel-checked `vm_compute; reflexivity`. It does not enumerate
or assume C executions. `increment8_spec_initial` extends the functional
denotation to any `CIMonad` interpretation of the core algebra.

## Build

Use Coq 8.17.1, CompCert 3.14 configured for x86-64, and VST 2.14 built against
that same CompCert. VST's `sha` libraries are an existing transitive dependency
of `Simplicity.Word` through `Simplicity.Alg`/`Digest`.

From the repository root in the configured Coq environment:

```sh
COMPCERT=/path/to/compcert VST=/path/to/VST bash Coq/build-jets.sh -j2
```

The tested local environment is:

```sh
env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  COMPCERT=/tmp/simplicity-compcert VST=/tmp/simplicity-vst \
  opam exec --switch=simplicity -- bash Coq/build-jets.sh -j2
```

The script generates a targeted makefile with dependency ordering and builds
**every module in `_CoqProject.jets`**, including `check_jet_assumptions.v`.
Previously it built only the audit target's dependency closure, which could
omit a listed experimental kernel; the W16 reader is now also explicitly
imported and printed by the audit. `Print Assumptions` is an inspection report,
not an automated axiom allowlist. It uses the normal logical name `C.jets`;
no `/tmp/jets.vo` or recursive `/tmp` load path is needed.

After building dependencies, the same script supports `--coqc`, `--coqtop`,
and `--coqchk`, forwarding remaining arguments with the project's load paths.
For example, in the environment above:

```sh
bash Coq/build-jets.sh --coqc -q C/jet_read16_layout_exec.v
bash Coq/build-jets.sh --coqtop -quiet
bash Coq/build-jets.sh --coqchk -silent C.jet_read16_layout_exec
```

Paths passed to these modes are relative to `Coq/`. They do not rebuild
dependencies; use the normal build after changing an imported module. Use
`--coqc` for final acceptance of a scratch proof: an interactive REPL can
continue after an error and its exit status alone is not proof completion.

The execution theorems inherit CompCert's existing classical logic,
functional extensionality, real-number decision axioms, and the parameterized
external-function/inline-assembly semantics appearing in the Clight relation.
No new axioms or assumed helper contracts are introduced. The value bridge and
monadic interpretation bridge are closed under the global context.

The strengthened public modules `C.jet_one8_position`, `C.jet_one8_crossing`,
and `C.jet_increment8_cursors` also passed `coqchk -silent` against the current
production AST with the same dependency load paths on 2026-09-22 (exit status 0).
The full targeted build and its final assumption audit passed after regenerating
that AST. This independently rechecks their
compiled proof objects; it does not remove the documented inherited assumptions.
The subsequent `add_8` milestone passed the targeted build, assumption audit,
and an independent `coqchk -silent C.jet_add8_spec` check on the same date.
Its symbolic value and monadic bridges are closed under the global context.
The output-crossing increment/add milestones subsequently passed the targeted
build, assumption audit, and
`coqchk -silent C.jet_increment8_crossing C.jet_add8_crossing` on the same date.
Crossing-byte interpretation is symbolic and closed under the global context.
The two-word-input increment/add milestones also passed the targeted build,
assumption audit, and
`coqchk -silent C.jet_increment8_two_words C.jet_add8_two_words` on the same date.
The crossing-read interpretation is closed under the global context.

On 2026-09-23, the general W16 crossing execution kernel passed direct `coqc`
and independent `coqchk -silent C.jet_read16_layout_exec`. The expanded build
of every module listed in `_CoqProject.jets`, including the updated W16
assumption audit, also passed (exit status 0). The reader execution results
inherit the same CompCert assumptions listed above; these checks do not yet
establish the logical-input bridge or complete `increment_16` equivalence.

## Reproduce the generated AST

`jet_translation_unit.c` includes the repository's real `C/frame.c` and
`C/jets.c`; it contains no copied/replaced implementations. Use the built
CompCert 3.14 `clightgen`, Clang as a **preprocessor only**, CompCert's supplied
standard headers, and genuine amd64 glibc headers.

The tested sysroot is Debian's `libc6-dev_2.36-9+deb12u14_amd64.deb`:

- URL: <https://deb.debian.org/debian/pool/main/g/glibc/libc6-dev_2.36-9+deb12u14_amd64.deb>
- SHA-256: `0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae`
- Extract `data.tar.xz` from the archive into a dedicated directory; do not
  install this Linux package over the host system.

```sh
COMPCERT=/path/to/compcert JET_SYSROOT=/path/to/extracted/sysroot \
  bash Coq/C/check-jets-generation.sh
```

`check-jets-generation.sh` writes only to a fresh temporary directory and
compares byte-for-byte without modifying the committed artifact. To regenerate
it deliberately, run `regenerate-jets.sh` without an output argument. Both use
`JET_ASSERTIONS=production` by default. Alternative `debug` and `reckless`
modes require an explicit output path and are not proof-coverage claims.
The debug artifact has been generated and compiled as Coq, but its executions
have not been proved. Invalid mode values and implicit alternate-mode
overwrites are rejected. The scripts retain generated files/configuration for
inspection. Paths used in the ini
must not contain whitespace or sed replacement metacharacters. Linux target
headers are selected explicitly, so Apple SDK headers cannot leak into the
translation. GCC/Clang feature-identification macros are suppressed for the
CompCert C frontend, as are native `__int128` extensions. C11 static assertions
are active. There are no replacement libc headers or edited generated bodies.

The older exploratory artifact used removed handwritten headers. Regeneration
with genuine glibc corrected, among other constants, `UINT8_MAX` from unsigned
`int` to `int`; the C arithmetic still performs unsigned multiplication via
`1U`. The proofs follow the regenerated AST's exact constant types.
