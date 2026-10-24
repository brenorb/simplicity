# Secp external-call semantics gaps

This is a proof-model limitation, **not a demonstrated mismatch between the
production C and the fixed Simplicity specification**. No implementation,
specification, API contract, generated AST or generation setting is changed.
The affected jets remain unresolved; these diagnostics add no coverage.

## Inversion: counting trailing zeroes is an abstract external call

Directly affected: `simplicity_fe_invert` and `simplicity_scalar_invert`.
Their C helpers call `secp256k1_modinv64_var`, whose divstep batches call
`secp256k1_ctz64_var`. Callers needing those inversions inherit this boundary;
this is not an exhaustive downstream call-graph claim.

For a nonzero 64-bit word, the needed helper contract is the number of trailing
zero bits, with unchanged memory and an empty trace. For example, argument 1
must return 0. The frozen production translation does not use the software
de Bruijn fallback: its unsigned-long-width guard is true and selects
`__builtin_ctzl`. The generated declaration is `EF_builtin "__builtin_ctzl"`
with signature `[Tlong] -> Tint`.

In the pinned CompCert 3.14, lookup for that name/signature returns `None`.
The alternate `__builtin_ctzll` also returns `None`. `builtin_or_external_sem`
therefore dispatches to the parameter `Events.external_functions_sem`, not to
a known counting function. The generic external-call properties specify no
ctz result and do not even guarantee that a call can return.

`jet_secp_ctz_semantics_gap.v` provides formal evidence for the actual guard,
callee and external declaration, both failed builtin lookups, and the dispatch
equation. Its `ctz_generic_properties_insufficient` is a closed countermodel
argument: the empty call relation satisfies `extcall_properties` but cannot
supply a result even for argument 1. This does **not** assign that relation to
CompCert's actual abstract parameter, demonstrate a stuck execution under a
chosen concrete library, or demonstrate an incorrect native C result. It
establishes that those generic properties alone cannot discharge the required
execution premise. The countermodel is diagnostic only, not a substitute
implementation or a semantics used by a registered jet proof.

`jet_secp_ctz_external_call.v` additionally proves the dependency through the
actual helper's execution, not merely its syntax. `eval_ctz64_requires_external`
extracts an `external_functions_sem "__builtin_ctzl"` call from any completed
execution of the original `secp256k1_ctz64_var`, with the same argument and
initial memory. It does not identify the extracted call's trace, result or
final memory with those of the complete helper. Conversely,
`eval_ctz64_from_external` constructs the complete original helper execution
when given an empty-trace external call returning an integer. That premise
remains explicit and unresolved; it does not assert a counting law, memory
preservation, or that such a call exists. These results use six inherited
assumptions, without the external-call determinism axioms. They do not yet
extract this call from a complete divstep batch or public inversion jet.

## Generation: wNAF also calls external memset

The original `secp256k1_ecmult_wnaf` calls `memset` to initialize its digit
array. The generated declaration is `EF_external "memset"`, with signature
`[Tlong; Tint; Tlong] -> Tlong`. The same diagnostic module formally checks
the declaration and the call in the actual helper body. Its mere presence
does not prove the zeroing behavior or the validity of a particular call's
arguments. `generate` and other ecmult callers still need a discharged
external-library boundary in addition to their arithmetic and execution
proofs. The scalar-splitting helper proof does not rely on memset or ctz.

`jet_secp_wnaf_entry15.wnaf_entry15_owned_output` additionally derives the
actual function entry and all eight preparation statements for the
generator's len=129/window=15 calls. It evaluates the real call arguments to
`(destination, 0, 516)`, preserves the destination's 516 Freeable bytes,
allocates the actual distinct 32-byte scalar local and preserves all old
memory up to the call. It assumes no zeroing or external-call execution.
This is positive execution evidence for entry/setup and valid destination
capacity, not a completed memset or wNAF call, nor an extraction theorem
from every completed public generate call. In particular, it supplies no
reason to identify the abstract external parameter with a concrete libc.
Build/check it with the commands below, substituting the target/module
`C/jet_secp_wnaf_entry15.vo` / `C.jet_secp_wnaf_entry15`.

## Internal normalization dependency

`jet_secp_modinv_normalize62_exec.eval_norm62_from_storage` derives the
complete original `secp256k1_modinv64_normalize_62` call from five owned
signed62 words and five read-only modulus words. It returns the exact
machine-word result, output ownership, unchanged modulus words/readability,
and framing outside the two 40-byte regions. The source need not be writable
or have nonnegative limbs. In particular, this interface does not exclude
the actual sparse field modulus's negative low limb.

This C-level dependency compiles and passes recursive kernel checking with
the same six inherited execution assumptions and no external-library model.
Its symbolic-run, return, output-shape and word-denotation certificates are
closed. It adds no registered jet: modular-inverse batch/loop composition
and ctz linkage are still required.
It is not a proof about the mathematical correctness of a jet specification
and does not repair or bypass the external-call boundary above.

`jet_secp_modinv_normalize62_global.eval_field_norm62_with_global` specializes
the call to the actual field-modulus global, reusing `modinfo_fe_limb` rather
than another modulus definition. It derives the call, exact output and
retained private ownership, and preserves the complete
`modinfo_fe_global_rep`: all 48 readable bytes and all six words, including
the untouched inverse coefficient at +40. Startup readiness is the existing
predicate established by `modinfo_fe_global_initializes`; neither an
initialized result nor a helper execution is assumed. This is still a
normalization dependency, not the public inverse jet.

`jet_secp_modinv_normalize62_numeric.norm62_field_machine_numeric` now proves
the numeric bridge for that exact machine-word result. For the helper's
internal signed-limb bounds and an aggregate input in `(-2*p,p)`, it returns
canonical nonnegative signed62 limbs whose value is `(sign*input) mod p`.
Here `sign` is -1 for a negative C sign argument and +1 otherwise. The proof
uses the actual sparse modulus, accounts for both conditional additions,
conditional bitwise negation and both signed carry passes, and proves that
the intermediate word additions do not overflow. Its numeric lemmas are
closed; `eval_field_norm62_numeric` composes them with the original C call
and retains ownership, all global metadata and byte-range framing, with the
same six inherited execution assumptions and no libc premise.

These are derived internal helper conditions, not new restrictions on
public jet inputs. The inverse loop must establish them. Neither a public
inversion equivalence nor additional jet coverage is claimed. Reproduce:

```sh
JET_TARGETS=C/jet_secp_modinv_normalize62_exec.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_exec
JET_TARGETS=C/jet_secp_modinv_normalize62_global.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_global
JET_TARGETS=C/jet_secp_modinv_normalize62_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_numeric
```

## Internal signed128 carry dependency

`jet_secp_i128_shift62.eval_i128_shift62_from_storage` executes the original
`secp256k1_i128_rshift` at the actual inverse-batch count 62, on arbitrary
initial 64-bit low/high words in writable 16-byte storage. Both stores are
derived from the initial permissions. It returns the exact cross-word low
result and the arithmetic-right-shifted high word, retaining permissions and
byte-range framing. In particular, the high-word shift is signed, not the
logical shift used by the existing unsigned shift helpers.

The symbolic-store adapter and `i128_shift62_oracle_correct` prove a summary
of that actual C call for use inside inverse batches; they do not postulate
an external implementation or add a libc premise. This reuses the existing
unsigned-shift proof structure and shared region/store lemmas. The complete
batch execution, loop invariants and public inversion composition remain
open, as does the ctz boundary above. This internal helper adds no jet coverage.

`jet_secp_i128_shift62_numeric.eval_i128_shift62_exact` additionally connects
that C execution to signed two-limb integer division by `2^62`, for every
initial 128-bit pattern. It derives the output's numeric equality together
with the actual call, exact output loads, permissions and framing, without
assuming nonnegative inputs or an intermediate output. The arithmetic bridge
reuses the existing checked signed-shift and signed/unsigned remainder lemmas;
it does not prove or replace the mathematical specification of a public jet.
Reproduce with the pinned dependencies:

```sh
JET_TARGETS=C/jet_secp_i128_shift62_oracle.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_i128_shift62_oracle
JET_TARGETS=C/jet_secp_i128_shift62_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_i128_shift62_numeric
```

### Internal signed multiplication dependency

`jet_secp_i128_mul_numeric.eval_i128_mul_exact` executes the original
`secp256k1_i128_mul`, including its call to the original `secp256k1_mul128`,
the private high-word allocation and its release. From an owned, initially
uninitialized 16-byte result region, it derives both output loads, their exact
signed 128-bit value `Int64.signed a * Int64.signed b`, the resulting ownership
and external byte-range framing. Both signed 64-bit inputs are unrestricted.
There is no assumed multiplication result or external-library behavior.

The arithmetic bridge follows the actual signed 32-bit partial-product
schedule. It reuses the unsigned helper's low-word, logical-shift and modular
return lemmas, but separately proves the signed cross-products, arithmetic
shifts and absence of signed overflow in the high-word additions. Treating
these as unsigned partial products would be incorrect for negative operands.
The pure observations are closed; the execution results retain the six
standing Coq/CompCert assumptions, not a new libc premise.

This closes the multiply stage used to initialize the inverse transition
accumulators. Transition-loop execution/invariants and the complete public
inversion composition remain open; so does the separate
ctz boundary described above. This internal result adds no public jet coverage
and changes no original C, generated AST, specification or external-call model.

```sh
JET_TARGETS=C/jet_secp_i128_mul_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_i128_mul_numeric
```

The subsequent `jet_secp_i128_accum_mul_numeric.eval_i128_accum_mul_numeric`
executes the original signed multiply-accumulate on arbitrary initial low/high
words and signed input words. It includes the actual private allocation/free
and discarded verification-expression branches. It derives exact output loads,
the sum modulo `2^128`, ownership and external framing. The closed
`smul_accum_exact_if_in_range` upgrades the modular observation to exact signed
addition whenever the mathematical sum is representable; this bound remains
an internal transition-invariant obligation, not an excluded public input.
The modular execution theorem requires no no-overflow premise and no new
external-helper assumption. This also adds no public jet coverage.

```sh
JET_TARGETS=C/jet_secp_i128_accum_mul_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_i128_accum_mul_numeric
```

### Transition initialization through both accumulator shifts

`jet_secp_modinv_fg_prefix_numeric.exec_fg_prefix_numeric` composes those
operations in the first sixteen actual statements of
`secp256k1_modinv64_update_fg_62_var`. It executes both signed products, both
multiply-accumulates, the discarded verification-expression branches and both
signed shifts. Its memory conclusions give the two accumulator words for
`(u*f[0] + v*g[0]) / 2^62` and `(q*f[0] + r*g[0]) / 2^62`, together with
ownership, temporary matching and byte-range framing. The proof checks that
all verification-expression branches have the same output regions.

The numeric result uses each transition matrix row's absolute sum bound
`<= 2^62` to derive representability, rather than assuming intermediate sums
or outputs. This is an internal divstep invariant still to be established at
the complete caller boundary. The length is symbolic, not fixed to one; the
prefix runs before the length-dependent loop. Local accumulator storage is
described by the actual `xalloc` result. The complete function's entry,
remaining loop, final stores and freeing of these locals remain to be
composed. The shift summary is proved for the original C function, not an
assumed helper implementation. There is no new libc premise and no public
jet registration or coverage increment.

```sh
JET_TARGETS=C/jet_secp_modinv_fg_prefix_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_prefix_numeric
```

The following loop support is also explicit:
`jet_secp_modinv_fg_index` proves the original signed62 indexed loads/stores,
including the actual `i - 1` expression, the loop comparison/increment and the
exit branch. Array offsets and signed-index conversions are derived, not
replaced by a constant-index C body. The loop's arithmetic body and complete
function composition remain open.

`jet_sx_void_oracle.pure_void_oracle_correct` provides a checked summary for
actual internal void calls whose symbolic branches all have identical output
regions, no events and no return value. It symbolically executes the original
function and checks every branch before returning a summary; differing results
cause failure. Its soundness derives the actual Clight call, ownership and
framing. This avoids duplicating the signed accumulation helper's discarded
verification-expression branches. It is not a libc model, assumed helper
behavior, a replacement implementation or a new public jet proof.

```sh
JET_TARGETS="C/jet_sx_void_oracle.vo C/jet_secp_modinv_fg_index.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_sx_void_oracle C.jet_secp_modinv_fg_index
```

## Reproduction and limits

With the pinned dependencies from `Coq/JET_BUILD.md`:

```sh
JET_TARGETS=C/jet_secp_ctz_semantics_gap.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ctz_semantics_gap
JET_TARGETS=C/jet_secp_ctz_external_call.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ctz_external_call
```

Inspect the named statements or the reviewed snapshots for their exact scope.
The lookup/countermodel evidence is formal. No native reproducer or native
wrong-result observation is claimed. In particular, this report does not
claim that a zero word is passed to a compiler builtin with a nonzero-input
contract; the divstep code adds a sentinel before counting.

The worst established consequence is an unresolved acceptance boundary for
the affected implementation-to-specification proofs, not a demonstrated
runtime failure, consensus discrepancy or exploit. A complete result needs
justified concrete external semantics/linkage; adding an unproved ctz or
memset premise would not meet the goal. Switching the production AST to a
fallback, changing compiler/generation configuration, or changing the target
would require separate explicit approval and is not done here.

