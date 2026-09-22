# C jet implementation-to-Simplicity proofs

## Public results and exact scope

`jet_increment8_spec.v:eval_increment8_matches_spec` constructs a complete
`ClightBigstep.Clight2.eval_funcall` of the generated
`f_simplicity_increment_8`, returning true with an empty trace. For every
`x : Word8`, its nine decoded output bits equal the functional evaluation of
the canonical Simplicity increment term. The term is the composition
`true &&& iden >>> full_increment word8`, where `full_increment` pairs the
input carry with the input word and a zero word before `full_add`.
This follows `Haskell/Core/Simplicity/Programs/Arith.hs`, not a replacement
integer addition specification.

`jet_one8_call.v:eval_one8_initial_matches_spec` does the same for
`f_simplicity_one_8` and `true >>> left_pad_low word1 word8`.

Both results prove the final output cursor is zero and preserve loads in
initially valid blocks other than the destination frame and output word.
Their premises contain **only initial memory facts and write permissions**.
Allocation, by-value source-frame copy, helper executions, stores, return
conversion, and deallocation are all proved. In particular, no successful
execution or successful intermediate store is assumed.

These are **concrete-layout results**, not all-layout jet equivalence:

- The target is x86-64, little-endian, LP64, using glibc integer typedefs.
- A frame is 16 bytes: pointer at offset 0, cursor at offset 8.
- Increment's source frame points one word past its input and has cursor 56.
  The input word contains the exact unsigned encoding of any `Word8`.
- The output frame points to a zero-initialized word and has cursor 9 for
  increment, or 8 for one. The output word and output frame are distinct
  blocks and writable in the stated locations.
- One's unused source frame must still be readable for its 16-byte C copy.
- The caller's environment argument is `Vundef`; neither jet uses it.
- Runtime assertions are disabled (`NDEBUG` and the library-required
  `RECKLESS` flag). Static assertions remain enabled and checked by clightgen.

Arbitrary initial output words, arbitrary cursor positions, cross-word writes,
other target ABIs, assertion-enabled builds, and `add_8` are not established
by these public theorems. No binary-level linking or native ARM execution
claim is made. The results are constructive terminating Clight executions,
not separate universal determinism/small-step theorems.

## Proof organization

- `jet_frame_copy.v`: copying raw `memval` bytes preserves frame pointer and
  cursor loads, including pointer fragments.
- `jet_exec.v`, `jet_one8.v`, `jet_read8.v`, `jet_write8.v`, `jet_writeBit.v`:
  actual generated helper bodies, memory accesses, calls, and function entry.
- `jet_increment8.v`: exact arithmetic expressions, casts, and statement tree.
- `jet_increment8_exec.v`: threads the actual three helper calls and derives
  their intervening loads from CompCert store-preservation lemmas.
- `jet_increment8_call.v`: constructs all intermediate memories from initial
  permissions and closes the complete function boundary.
- `jet_spec.v`: canonical primitive Simplicity terms and parametricity.
- `jet_increment8_spec.v`, `jet_one8_call.v`: public C-to-Simplicity results.

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
