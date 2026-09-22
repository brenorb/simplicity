# C jet implementation-to-Simplicity proofs

## Public results and exact scope

`jet_increment8_general.v:eval_increment8_frame_matches_spec` constructs a complete
`ClightBigstep.Clight2.eval_funcall` of the generated
`f_simplicity_increment_8`, returning true with an empty trace. For every
`x : Word8`, its nine decoded output bits equal the functional evaluation of
the canonical Simplicity increment term. The term is the composition
`true &&& iden >>> full_increment word8`, where `full_increment` pairs the
input carry with the input word and a zero word before `full_add`.
This follows `Haskell/Core/Simplicity/Programs/Arith.hs`, not a replacement
integer addition specification.

`jet_one8_position.v:eval_one8_position_matches_spec` does the same for
`f_simplicity_one_8` and `true >>> left_pad_low word1 word8`, at any output
cursor from 8 through 64. It decodes the byte at bits `[cursor-8, cursor)`.
The previous fixed-cursor and zero-initialized theorems remain checked
corollaries/regression tests.

Both results prove the final output cursor (zero for increment, `cursor-8`
for one) and preserve loads in
initially valid blocks other than the destination frame and output word.
Their premises contain **only initial memory facts and write permissions**.
Allocation, by-value source-frame copy, helper executions, stores, return
conversion, and deallocation are all proved. In particular, no successful
execution or successful intermediate store is assumed.

These are **concrete-layout results**, not all-layout jet equivalence:

- The target is x86-64, little-endian, LP64, using glibc integer typedefs.
- A frame is 16 bytes: pointer at offset 0, cursor at offset 8.
- Increment's source frame points one word past its input and has cursor 56.
  Only its low eight bits must encode the input `Word8`; the other 56 bits
  are arbitrary.
- The output frame points to an initialized but otherwise arbitrary word
  and has cursor 9 for increment, or any cursor in `[8,64]` for one.
  The output word and output frame are distinct blocks and writable in the
  stated locations. Increment preserves the other 55 bits; one preserves
  all bits at or above its initial cursor (the already-written prefix).
  C's writer may clear unused bits below the output slice; their preservation
  is intentionally not required.
- One's unused source frame must still be readable for its 16-byte C copy.
- The caller's environment argument is `Vundef`; neither jet uses it.
- Runtime assertions are disabled (`NDEBUG` and the library-required
  `RECKLESS` flag). Static assertions remain enabled and checked by clightgen.

Cross-word writes, general input/output cursor positions for increment,
nonzero frame/backing-word base offsets, other target ABIs, assertion-enabled
builds, and `add_8` are not established by these public theorems. No binary-level linking or native ARM execution
claim is made. The results are constructive terminating Clight executions,
not separate universal determinism/small-step theorems.

## Proof organization

- `jet_frame_spec.v`: reusable bit/cursor/address predicates and the concrete
  single-word input/output contracts used by the public theorems. The more
  general predicates are representation infrastructure, not yet all-layout
  execution contracts; future execution results must establish address bounds
  and permissions for each accessed cell.
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
- `jet_exec.v`, `jet_one8.v`, `jet_read8.v`, `jet_write8.v`, `jet_writeBit.v`:
  actual generated helper bodies, memory accesses, calls, and function entry.
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
- `jet_increment8_general.v`, `jet_one8_position.v`: strongest public
  C-to-Simplicity results. `jet_increment8_spec.v`, `jet_one8_general.v`, and
  `jet_one8_call.v` retain the earlier special cases.

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

The strengthened public modules `C.jet_one8_position` and
`C.jet_increment8_general` also passed `coqchk -silent` with the same dependency
load paths on 2026-09-22 (exit status 0). This independently rechecks their
compiled proof objects; it does not remove the documented inherited assumptions.

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
  bash Coq/C/regenerate-jets.sh /tmp/jets-check.v
cmp Coq/C/jets.v /tmp/jets-check.v
```

Omit the output argument to regenerate the committed artifact. The script
retains its generated configuration for inspection. Paths used in the ini
must not contain whitespace or sed replacement metacharacters. Linux target
headers are selected explicitly, so Apple SDK headers cannot leak into the
translation. GCC/Clang feature-identification macros are suppressed for the
CompCert C frontend, as are native `__int128` extensions. C11 static assertions
are active. There are no replacement libc headers or edited generated bodies.

The older exploratory artifact used removed handwritten headers. Regeneration
with genuine glibc corrected, among other constants, `UINT8_MAX` from unsigned
`int` to `int`; the C arithmetic still performs unsigned multiplication via
`1U`. The proofs follow the regenerated AST's exact constant types.
