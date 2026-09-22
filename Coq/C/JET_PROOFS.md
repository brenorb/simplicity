# C jet implementation-to-Simplicity proofs

## Public results and exact scope

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

These are **concrete-layout results**, not all-layout jet equivalence:

- The target is x86-64, little-endian, LP64, using glibc integer typedefs.
- A frame is 16 bytes: pointer at offset 0, cursor at offset 8.
- Increment's source frame points one word past its input and has any cursor
  from 0 through 56. The eight bits beginning at that cursor encode the input
  `Word8`; every other input bit is arbitrary. Input and output cursors vary
  independently. The generalized reader includes cursor 48, needed before
  the second read at cursor 56 in a two-operand byte jet.
  Add's source frame has the same base layout and cursor 0..48; its two
  consecutive byte slices encode the input pair.
- The output frame points to an initialized but otherwise arbitrary word
  and has any cursor in `[9,64]` for increment/add, or `[8,64]` for the single-word
  one theorem. The crossing one theorem uses two initialized words and a
  cursor in `[65,71]`.
  The crossing increment/add theorems use two initialized words at offsets
  8 and 0 and a cursor in `[65,72]`, preserving the high word's written prefix.
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

Input-crossing paths, nonzero frame/backing-word base offsets,
other target ABIs, fully debug-enabled execution (without `PRODUCTION`),
and larger-width arithmetic jets are not established by these public theorems.
No binary-level linking or native ARM execution
claim is made. The results are constructive terminating Clight executions,
not separate universal determinism/small-step theorems.

## Proof organization

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
- `jet_read8_position.v`, `jet_writeBit_position.v`: actual helper execution
  at all in-word read and carry-bit cursors.
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
  strongest public C-to-Simplicity results. Earlier modules retain the
  fixed-layout special cases.
- `jet_increment8_crossing.v`, `jet_add8_crossing.v`: full jet equivalence
  for crossing outputs, with actual reads, frame copies, allocation and freeing.

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

The script generates a targeted makefile with dependency ordering. It uses the
normal logical name `C.jets`; no `/tmp/jets.vo` or recursive `/tmp` load path is
needed. `check_jet_assumptions.v` is the final build target.

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
