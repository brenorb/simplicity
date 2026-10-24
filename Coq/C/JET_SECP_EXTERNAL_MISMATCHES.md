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

`jet_secp_modinv_fg_iteration_prefix.exec_fg_iter_prefix` uses that checked
summary to execute the original loop's two operand loads and four signed
multiply-accumulates, for every valid nonzero index 1 through 4 of the actual
five-limb objects. Both accumulators may initially contain arbitrary words.
Its postcondition derives the exact symbolic output words, ownership,
temporaries and framing; no intermediate execution or output is assumed.
The checked source split retains the actual masked stores and shifts as the
remaining suffix. This prefix alone does not establish full-loop induction,
its numeric invariant or caller composition. It adds no public jet coverage.

`jet_secp_modinv_fg_iteration.exec_fg_iteration` then completes the original
loop body: it derives both computed-index masked stores and both signed
accumulator shifts, as well as the preceding loads/accumulations, at all four
valid nonzero limb indices. Its postcondition retains exact symbolic output
regions, temporary matching and byte-range framing. The store adapter derives
permissions and actual `Mem.store` effects from represented initial storage;
no store, helper execution or output is assumed by the body theorem.

The proof-side stage states distinguish indices 1 through 4 before computing
the actual calls. Each case is checked against the original statement run;
this keeps symbolic-index conversion from expanding a large interpreter term.
It is not a different C body or an excluded valid loop index. All proofs close
under the ordinary ten-second command limit. This is a complete **body**
execution theorem, not a complete loop, inverse helper or public jet proof.
The full-loop invariant, final stores, entry/freeing and full caller composition
are still open; no public coverage increment is claimed.

`jet_secp_modinv_fg_iteration_numeric.exec_fg_iteration_numeric` connects this
same original body execution to the radix-`2^62` recurrence for both rows.
It derives the physical masked-limb and carry loads, their remainder/quotient
values, and exact recombination of the pre-shift sum. The shared arithmetic
proof derives the absence of signed-128 overflow from internal carry, matrix-row
and limb bounds, and proves preservation of the carry bound for induction.
Those internal bounds must still be established by the full caller; they do
not restrict a registered jet's input or add an execution/library assumption.
This is a numeric **body** result, not the full loop or public inversion proof.

`jet_secp_modinv_fg_loop.exec_fg_loop_from_body` composes the actual loop
guard, checked body, index increment and exit by induction. It covers all
remaining iteration counts with `1 <= k <= k+count <= 5`, retaining exact
machine-word state, ownership, temporary bindings and byte-range framing.
The revaluation layer derives the next iteration's represented storage from
the previous actual output; it does not assume loads or stores. This closes
the loop's execution composition, but the numeric invariant over the entire
radix value, final stores, allocation/freeing and inverse caller composition
are still separate obligations. There is no new public coverage entry.

`jet_secp_modinv_fg_loop_numeric.exec_fg_loop_numeric` adds the full-loop
numeric invariant to that actual execution. The decoded low output limbs
and final signed-128 carry equal the initial carry plus the remaining
matrix-weighted input limbs, with exact radix-`2^62` weights. It proves
preservation of the internal limb, row and carry bounds rather than assuming
them at each iteration. The arithmetic invariant is closed; the combined
execution theorem uses only the same six inherited assumptions. Initial
bounds, the prefix-to-loop handoff, final carry stores, function entry/freeing
and the complete inverse caller are still to be composed. This loop theorem
is not a public jet proof and does not change coverage.

`jet_secp_modinv_fg_finish_numeric.exec_fg_loop_and_finish` then composes
the checked loop with both original `i128_to_i64` calls and the final indexed
stores into `f` and `g`. It derives all active output-word loads and their
signed-radix value, ownership, temporaries and framing. The cast bridge proves
that a carry representable as signed-64 is stored without changing its value;
the loop preserves that range from the initial carry and the internal state
bounds. No call, store or output is assumed. The initial prefix must still
establish those bounds and hand off its actual state, and function entry,
allocation/freeing and the full inverse caller are not yet composed. This
remains a transition-helper result, not another registered jet.

`jet_secp_modinv_fg_body.exec_fg_body` connects that suffix to the original
prefix and proves the **complete original transition body**. From represented
initial arrays and internal matrix/limb bounds it derives every active output
load, its signed-radix value `(u*f+v*g)/2^62` (and the second row), ownership,
live temporaries and framing. The handoff proves the initial carry values,
bounds and signed-64 representability; none is assumed as a new intermediate
premise. Its quotient statement does not assume divisibility: the inverse
caller still has to supply the actual divstep matrix and discharge its own
invariants. This closes body composition, not function entry/allocation/freeing
or the complete public inversion jet. No coverage entry is added.

`jet_secp_modinv_fg_call.eval_fg_transition` closes the original transition
**function call**, including actual function entry, local allocation, body,
void result and freeing. It derives all active output loads, the two row
quotients, output ownership and caller-memory framing. The shared lifecycle
lemma now admits an explicit internal precondition and a revalued final word
state; the previous unconditional/identity-state interface is retained as a
proved corollary with the same contract. No production function or helper
execution is substituted. The variable inverse still needs the actual divstep
and coefficient-update calls and the full caller invariant; the read-only
matrix contract also does not itself restore a caller's stronger matrix
ownership. This function theorem adds no public jet coverage.

`jet_secp_modinv_fg_permissions.eval_fg_transition_matrix_permissions`
adds the missing **matrix permission-retention fact** for a caller that
initially owns the matrix's 32 Freeable bytes. It preserves all conclusions
of the original variable-length transition call and proves those bytes
remain Freeable afterwards. The earlier read-only contract is unchanged;
the stronger internal caller precondition buys a stronger conclusion,
not a restriction added to a public jet.

`jet_clight_internal_permissions.internal_exec_keeps_permissions` supplies
the reusable proof: a checked closed table of original internal C functions
preserves pre-existing permissions. Stores preserve them, function entry
allocates fresh blocks, and the final freeing of locals avoids every
pre-existing block. The secp adapter checks the actual seven-function
call graph, linkage, non-function locals and absence of external/builtin
calls. No external-call semantics or permission-preservation premise is
assumed. Rebuilding a complete inverse-caller representation and composing
its loop remain separate obligations; this result adds no public coverage.

`jet_secp_modinv_fg_owned.eval_fg_transition_owned` restores the stronger
represented matrix ownership required by the inverse caller. It starts
with an owned matrix and derives the complete original transition call,
the same output-word/value results, and a post-representation with all
32 matrix bytes still owned. The proof weakens only the internal input
representation when applying the existing read-only theorem, then derives
the stronger post-representation from the proved Freeable permissions,
the retained loads and separation from the two owned arrays. No output
ownership or separation is assumed. The prior read-only interface remains
unchanged. This closes the matrix representation gap, not the whole inverse
caller or its divstep/termination obligations, and adds no public coverage.

`jet_secp_modinv_de_exec.eval_de_words` executes the original coefficient
update `secp256k1_modinv64_update_de_62` with the actual field-modulus metadata,
including entry, both private accumulators, every original call/store, return
and freeing. It derives exact output-word loads, owned `d/e` arrays and matrix,
the read-only metadata and caller-memory framing. The output words are still
the execution-derived machine expressions: their modular-value and range
bridge to the inverse invariant is not yet proved or claimed.

`jet_sx_known` proves constant-condition selection against the unchanged
Clight statement. It evaluates the original condition and its C boolean
conversion, and selects a branch only when the result is proved independent
of the symbolic inputs. Unknown cases retain the existing executor. This
avoids exploring the impossible nonzero branches of the three zero field
modulus limbs; it changes no generated C/AST, assertion setting or external
semantics. Both the branch checker and this actual helper call are proof
dependencies, not new public jet coverage.

`jet_secp_modinv_de_correction_numeric.exec_de62_correction_values` connects
the original coefficient-update prefix to its arithmetic meaning. From
represented arrays and the internal divstep matrix-row bounds it derives
the actual `_md`/`_me` temporary values, their signed-64 representability,
and divisibility of both corrected low accumulators by `2^62`. The prefix
includes the original signed products, accumulations, low-word accessors
and correction assignments; no intermediate execution or output is assumed.
The proof uses the actual negative low field-modulus limb `-4294968273`
and the original inverse metadata. This closes the low-word correction
step, not the five-limb coefficient value/range invariant or the complete
public inversion jet. Those obligations and the caller's divstep bounds
remain; no coverage entry is added.

`jet_secp_modinv_de_recurrence_words.eval_de_recurrence` relates the whole
original coefficient-update call to an explicit five-limb machine recurrence.
A checked comparison covers all ten actual output words, including the
negative low-modulus correction, three zero middle modulus limbs, the final
`256` modulus limb and both final signed-carry stores. Denotation lemmas link
the symbolic recurrence to the actual `Int64` multiply-accumulate and shift
operations. The result retains the existing entry/freeing, ownership and
framing guarantees and assumes only the original represented inputs. This
is a machine-word recurrence bridge, not yet its integer-value/range proof
or a complete public inversion theorem; public coverage is unchanged.

`jet_secp_modinv_de_call.eval_de_transition` closes that coefficient-update
integer-value/range bridge for the **complete original C helper call**.
From represented inputs, the internal matrix-row bounds, and the input
limb/value invariant, it derives every stored word, the exact row value
`(u*d + v*e + p*correction)/2^62`, preservation modulo the field order,
and the original strict output limb and `(-2p,p)` value bounds. The
signed-128 accumulator bounds, signed-64 final carries and initial
divisibility are proved from those internal inputs, not assumed. The proof
reuses the existing normalization arithmetic to bound the sign-adjusted
coefficient values. Entry, local allocation/freeing, output ownership
(including the matrix) and caller-memory framing come from the actual
execution proof; no alternative implementation or external model is used.

The numeric lemmas are closed. This helper result does not itself establish
the divstep matrix, its row bounds or the variable inverse caller's loop
invariants/termination; those remain required for the public inversion jet,
as does the reported external-call boundary. No coverage entry is added.

`jet_secp_modinv_de_revalue.eval_de_step` closes the coefficient-state
handoff: the actual helper returns memory representing `de62_next_rho`
under the same owned-array/matrix and read-only metadata layout. The
result derives the next state's limb/value bounds and its scaled exact
and modular row relations. The matrix row values are unchanged by this
coefficient update. Representation transport uses the existing 64-bit
region transport lemma; a small abstract four-region assembly proof avoids
expanding the large symbolic word expressions during kernel conversion.
No ownership, output state, bound or helper execution is assumed as a new
premise. This makes the coefficient helper reusable by the inverse loop;
it is not a proof of that caller's divsteps or termination and adds no
public jet coverage.

`jet_secp_modinv_var_entry.inv_entry_and_initializers` begins the original
`secp256k1_modinv64_var` caller itself. From represented input words and
read-only field metadata it derives actual function entry, allocation of
the five original local objects, parameter binding and execution of the
ten original `d=0`/`e=1` initializer stores. The resulting memory represents
the initialized coefficients, with their initial limb/value invariant,
owned private objects, fresh-local separation and caller-memory framing.
Future matrix values remain arbitrary: this theorem does not claim that
the as-yet-uninitialized matrix contains zeroes. The initialized values are
connected to actual loads, not merely to a separately specified initial
state. This prefix stops **before both original struct-copy calls**; those
copies, `len`/`eta` setup, the divstep loop and whole-function return/freeing
remain unproved here. No external-helper behavior or later execution is
assumed, and no public jet coverage is added.

`jet_secp_modinv_var_copies.inv_entry_to_loop` extends that entry prefix
through the two original `signed62_assign` calls and the original
`len=5`/`eta=-1` setup. Both calls reuse the checked Clight by-copy
implementation, not libc or a replacement sequence of stores. Their
source readability, destination ownership and separation are derived
from the caller's represented state. The resulting seven-region state
retains the initialized coefficients, represents the copied modulus and
input, and preserves the uninitialized matrix without inventing values.
All five local allocations, parameter binding, actual prefix execution,
fresh-local separation and caller-memory framing are conclusions. The
specialized entry uses metadata at block offset zero, as for the actual
constant global; it adds no restriction on the five input words. The
divstep loop, its invariant/termination and whole-function return/freeing
remain required. No external-helper behavior is assumed, and this caller
prefix adds no public jet coverage.

`jet_secp_modinv_var_zero.exec_inv_zero_test` executes the original caller's
post-transition zero-test for every active length 1 through 5. Its actual
Clight outcome is `Out_break` exactly when all active `g` words are zero.
The bounded OR-accumulation loop is proved directly by its remaining limb
count; every array read is in range. The memory is exactly unchanged, as
are all temporaries other than the four actually assigned by this test.
There is no premise about a callee, an execution, a result, or a library
model. The numerical corollary relates that same break outcome to the
signed62 integer being zero under the internal nonnegative lower-digit
bounds, without restricting the top word. These bounds remain caller-loop
invariant obligations, not added public-input preconditions. The subsequent
limb-shortening code, divstep execution, invariant composition and complete
inverse call remain unproved; this control-flow result adds no coverage.

`jet_secp_modinv_var_shorten.exec_inv_shortening_numeric` executes the
original subsequent limb-shortening section for every active length 1
through 5. The guard is proved true exactly when at least two limbs remain
and both top words are zero or minus one. The length-one case therefore
cannot perform either out-of-range store. In the true branch both actual
Clight stores are derived and the active length decreases by one; in the
false branch memory and length are unchanged. All five output words in
each array, continued ownership, the new length's range and preservation
outside the two array blocks are conclusions. Other temporaries are
preserved except the six assigned by this section.

Under the internal nonnegative lower-digit bounds, sign propagation
preserves each signed62 integer exactly and retains those lower-digit
bounds for the next iteration. This is connected to the actual output
loads, not a replacement arithmetic operation. The numeric lemmas are
closed; the execution uses the six inherited execution assumptions and
no extra external-library model. The divstep call, complete loop
invariant/termination composition and whole inverse return/freeing remain
required. No public jet coverage is added.

`jet_secp_modinv_var_post.exec_inv_post_ready` composes the actual zero-test
and shortening statements in the original caller's order, including the
early `Out_break` that skips shortening. It returns a represented control
state over the same owned layout, with updated words and active length,
retained nonnegative lower digits and exact preservation of both integer
values. Breaking is equivalent to the represented `g` being zero; normal
continuation implies the next represented `g` is nonzero. Unrelated
temporaries and memory outside the two array blocks are preserved.

The representation handoff is derived from the actual output loads and
ownership, reusing the existing owned-word-region construction. It is not
an assumed post-state or later execution. This closes the post-transition
control only: the preceding divstep/update calls still need composition
with the full caller invariant, and whole-loop termination, final
normalization/copy-back and return/freeing remain required. No external
model is added and no public jet coverage is claimed.

`jet_secp_modinv_var_de.exec_inv_de_caller` connects the already proved
coefficient update to its actual `Scall` in the original inverse loop. Its
argument evaluation and helper layout are derived from the seven-region
caller representation and the caller's actual local environment. After the
call, all seven regions remain represented: the updated `d` and `e`, the
unchanged transition matrix and modulus metadata, and the untouched input,
`f` and `g`. The coefficient state bounds and both exact scaled-value and
modular relations come from the checked helper execution, not assumed
postconditions. The current module uses the six inherited execution
assumptions and adds no external-library model.

The row and coefficient bounds are internal preconditions still to be
established by the complete caller invariant and divstep execution. This
does not prove the preceding divstep call, the subsequent `f`/`g` update in
the caller, whole-loop termination, final normalization/copy-back or the
inverse return/freeing. It adds no public jet coverage and does not resolve
the separately documented external-semantics boundary.

`jet_secp_modinv_var_fg.exec_inv_fg_ready` connects the actual subsequent
`f`/`g` helper call to the same seven-region caller state. All five stored
words in each array, including inactive limbs, are related to the helper's
actual result. The represented active integers equal the checked matrix
quotients, and every lower active digit is nonnegative and below `2^62`.
Those lower-digit bounds follow from the actual masking operations, without
assuming the initial sparse modulus already has nonnegative lower limbs.
The input, coefficients, metadata and owned transition matrix remain
represented after the call.

`exec_inv_update_calls` composes the original coefficient and `f`/`g` calls
in their actual order. It derives the second call's representation from
the first call's result, proves that the first update leaves the second
update's input bounds unchanged, and retains both numeric results and a
combined memory frame. Neither callee execution nor its output is assumed.
The statements use the six inherited execution assumptions and no new
external-library model. The internal coefficient/matrix and `f`/`g` bounds
still require the divstep and complete caller invariant. The divstep call,
composition with the zero-test/shortening control, loop termination, final
normalization/copy-back and complete inverse return/freeing remain open.
This is supporting proof progress, not a registered inverse jet proof.

`jet_secp_modinv_var_tail.exec_inv_after_divsteps` composes the actual
remaining loop-body suffix: coefficient update, `f`/`g` update, zero-test
and conditional limb shortening. `inv_after_divsteps_source` identifies
that suffix in the original generated caller body. Its proof derives the
control section's representation and lower-digit bounds from the two
actual update calls. It then restores all seven initialized caller regions,
including the coefficients and transition matrix, using the actual memory
frame rather than the control helper's deliberately weaker representation.

The final represented coefficients retain their bounds, exact scaled-value
and modular relations. The final active `f`/`g` integers retain the matrix
quotients through shortening, with valid active length and lower digits.
Breaking is equivalent to the final represented `g` being zero; normal
continuation implies it is nonzero. The actual length temporary, unrelated
temporaries and the combined memory frame are included in the result.
The numeric projection lemmas are closed and the execution uses only the
six inherited execution assumptions, with no new external-library model.

This still requires the internal bounds supplied at the suffix's entry.
It does not execute the preceding divstep/eta prefix, establish the full
inverse invariant or termination, or prove final normalization/copy-back
and return/freeing. No public jet coverage is added.

`jet_secp_modinv_var_finish.exec_inv_finish` executes the original finishing
statements after the inverse loop: the actual load of `f.v[len-1]`, the
`normalize_62` call and the original signed62 struct-copy call back to `x`.
Both calls are connected to the caller's actual arguments and local
environment. The output in `x` and `d` is canonical signed62 storage and
its unsigned value is the signed coefficient, reduced modulo the field
prime. Continued ownership of both objects, readiness of the complete
48-byte modulus global and the actual memory frame are conclusions.

This result is for the field invocation's actual named modulus global at
offset zero, not arbitrary modulus pointers. Its readiness is derived
from the existing caller representation rather than assumed separately.
The original `normalize_62` and struct-copy proofs are reused; no external
library model is introduced. The numeric projection lemmas are closed and
the execution has the six inherited execution assumptions.

The coefficient bounds remain internal preconditions supplied by the
loop. Proving that this coefficient is the requested inverse still needs
the complete loop invariant, divstep execution and termination, and the
whole-function allocation/return/free composition remains open. This
finishing-path result alone adds no public jet coverage.

`jet_secp_modinv_var_free.exec_inv_finish_and_free` executes the finishing
statements and proves that CompCert's actual `free_list` on
`blocks_of_env secp_ge e` succeeds. The five local blocks, their sizes and
their non-duplication are derived from the real caller environment and
generated allocation map. The needed final permissions come from the
checked normalization/copy-back result and its memory frame, not a new
permission or execution premise.

The canonical output in `x`, its unsigned modular-value relation and its
ownership survive local reclamation; the complete modulus-global readiness
and the external memory frame also survive. The local `d` object is freed
and is deliberately not claimed as live output afterward. The helper uses
only the six inherited execution assumptions and no external-library model.

This closes local reclamation after the finishing path, not the entire
inverse call. The actual entry, complete divstep/loop execution, invariant
and termination still need composition, including the argument that the
normalized coefficient is the requested inverse. No public jet coverage
is added by this internal finishing-and-freeing theorem.

`jet_secp_modinv_var_invariant.exec_inv_after_divsteps_invariant` strengthens
the actual suffix execution with preservation of the input/coefficient
relation: `input*d = f (mod p)` and `input*e = g (mod p)`, using the values
represented by the caller's actual words. It retains the checked execution,
memory/temporary results, coefficient bounds and numeric output relations.
The final represented `f`/`g` state is related to 62 integer divsteps of
the initial represented state, including after any limb shortening.

The proof uses the C coefficient-update equality, its actual `f`/`g`
quotients and the existing `Trans.transN_step` theorem. Divisibility by
`2^62` is derived from that matrix theorem; cancellation modulo the actual
field prime is proved by a closed coprimality check. It does not assume a
new matrix-divisibility fact, a callee execution or an output state in the
composed execution theorem. These arithmetic bridge lemmas are closed;
the execution retains the six inherited assumptions and no library model.

The correspondence between the four represented matrix words and the
62-divstep transition remains an explicit internal precondition, together
with the entry invariant and row/limb bounds. Executing the original C
divstep routine and deriving that matrix correspondence is still required,
as are full-loop invariant/termination composition and the canonical
inverse argument, including zero input. This result adds no public jet
coverage and does not discharge the external ctz boundary.

```sh
JET_TARGETS="C/jet_sx_void_oracle.vo C/jet_secp_modinv_fg_index.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_sx_void_oracle C.jet_secp_modinv_fg_index
JET_TARGETS=C/jet_secp_modinv_fg_iteration_prefix.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_iteration_prefix
JET_TARGETS=C/jet_secp_modinv_fg_iteration.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_iteration
JET_TARGETS=C/jet_secp_modinv_fg_iteration_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_iteration_arith C.jet_secp_modinv_fg_iteration_numeric
JET_TARGETS=C/jet_secp_modinv_fg_loop.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_revalue C.jet_secp_modinv_fg_loop
JET_TARGETS=C/jet_secp_modinv_fg_loop_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_loop_numeric
JET_TARGETS=C/jet_secp_modinv_fg_finish_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_finish C.jet_secp_modinv_fg_finish_numeric
JET_TARGETS=C/jet_secp_modinv_fg_body.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_body
JET_TARGETS=C/jet_secp_modinv_fg_call.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_multiply_call_lifecycle C.jet_secp_modinv_fg_call
JET_TARGETS=C/jet_secp_modinv_fg_permissions.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_clight_internal_permissions C.jet_secp_modinv_fg_permissions
JET_TARGETS=C/jet_secp_modinv_fg_owned.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_fg_owned
JET_TARGETS=C/jet_secp_modinv_de_exec.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_sx_known C.jet_secp_modinv_de_exec
JET_TARGETS=C/jet_secp_modinv_de_correction_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_de_correction C.jet_secp_modinv_de_correction_numeric
JET_TARGETS=C/jet_secp_modinv_de_recurrence_words.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_de_recurrence C.jet_secp_modinv_de_recurrence_words
JET_TARGETS=C/jet_secp_modinv_de_call.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_call
JET_TARGETS=C/jet_secp_modinv_de_revalue.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_de_revalue
JET_TARGETS=C/jet_secp_modinv_var_entry.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_entry
JET_TARGETS=C/jet_secp_modinv_var_copies.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_copies
JET_TARGETS=C/jet_secp_modinv_var_zero.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_zero
JET_TARGETS=C/jet_secp_modinv_var_shorten.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_shorten
JET_TARGETS=C/jet_secp_modinv_var_post.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_post
JET_TARGETS=C/jet_secp_modinv_var_de.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_de
JET_TARGETS=C/jet_secp_modinv_var_fg.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_fg
JET_TARGETS=C/jet_secp_modinv_var_tail.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_tail
JET_TARGETS=C/jet_secp_modinv_var_finish.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_finish
JET_TARGETS=C/jet_secp_modinv_var_free.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_free
JET_TARGETS=C/jet_secp_modinv_var_invariant.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_invariant
```

## Post-inversion affine arithmetic (internal progress, no added coverage)

`jet_secp_gej_affine_arithmetic.exec_affine_arithmetic` composes the original
square and three multiply calls from `secp256k1_ge_set_gej_var`, after the
in-place inversion of its Z coordinate. `affine_arithmetic_source` checks
the statement context against the unchanged generated function body. The
cube-call adapter in `jet_secp_gej_affine_cube.v` reuses the checked field
multiplier at the caller's actual layout: fresh 40-byte output, Z at offset
80 in an owned 128-byte point, and the separate squared temporary.

For bounded field limbs X, Y, and the **already-inverted** field zi, the
composed theorem derives execution of all four calls, exact output limbs,
reusable bounds, and X * zi^2 / Y * zi^3 congruences modulo the field prime.
It retains ownership of the point and both local temporaries, preserves Z
and both computed temporaries, and frames all memory outside the point's
three field slices and the temporaries (including the infinity flag).
The temporaries need not be initialized before the first writes. The
intermediate call executions and memory-preservation facts are derived,
not new execution premises.

This arithmetic theorem is an **internal prefix**, expressed with a terminal `Sskip`;
it does not execute the preceding inversion, the subsequent Z=1/set_xy
statements, function entry or local reclamation. In particular, zi is not
claimed to be the inverse of a supplied original input. The subsequent
statements and reclamation are addressed below; inversion, function entry,
the infinity branch, and the public Simplicity composition remain to be
discharged for `gej_normalize` / `gej_y_is_odd`. No new external model or
public jet registration is introduced; coverage remains 514/533.

```sh
JET_TARGETS="C/jet_secp_gej_affine_cube.vo C/jet_secp_gej_affine_arithmetic.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_affine_cube C.jet_secp_gej_affine_arithmetic
```

`jet_secp_ge_set_xy.eval_ge_set_xy_owned` executes the original affine
constructor's Mint32 infinity-flag store and both 40-byte Clight struct
assignments. It accepts an uninitialized owned destination, returns its
exact X/Y fields and zero flag, preserves all permissions, and frames every
other block. It reuses `exec_field_copy_owned`, not a libc model or a
replacement implementation.

`jet_secp_gej_affine_finish.exec_affine_after_inverse` extends the arithmetic
prefix through the actual Z=1 and `ge_set_xy` calls. The original statement
context is retained; intermediate call execution, ownership, and preservation
are all derived. The output point has Z=1, the affine result has the exact
computed coordinates and zero infinity flag, and the congruences and bounds
from the arithmetic prefix are retained. The point's original infinity flag
and unrelated memory remain framed.

`exec_affine_after_inverse_and_free` additionally derives the original
`Mem.free_list` for `blocks_of_env secp_ge (affine_local_env b2 b3)` and proves
that the affine fields, flag, numeric facts, and both caller-owned allocations
survive reclamation. The two temporary fields are not claimed to remain owned
after they are freed. Their required ownership and distinctness follow from
the explicit internal preconditions; deriving those from actual function entry
is still a caller-composition obligation.

These results start **after inversion**, with represented bounded X, Y, zi,
and distinct owned caller/local allocations. They do not assert that zi is
the inverse of the original input. The preceding inversion and finite/infinite
branch selection, complete function-entry composition, and public frame/spec
bridges are not completed by this suffix. Coverage is still 514/533; no extra
external-library premise or public registration has been added.

```sh
JET_TARGETS="C/jet_secp_ge_set_xy.vo C/jet_secp_gej_affine_finish.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ge_set_xy C.jet_secp_gej_affine_finish
```

## Original field-inverse preparation (internal progress, no added coverage)

`jet_secp_fe_inv_prefix.fe_inv_entry_to_core` derives actual entry into
`secp256k1_fe_inv_var`, both original local allocations, the initial Clight
struct copy, and the two original normalization/signed62-conversion calls.
Its source identification is checked against the unchanged generated body.
It accepts a represented bounded field at any valid slice offset, including
the Z-at-80 input used by affine conversion; input and eventual output
pointers need not be distinct. The output pointer is only bound at this
prefix, not dereferenced or claimed to have been written.

The result supplies the actual core's `inv_start_regs` representation over
the packed temporary and named modulus global, with canonical signed62
words whose unsigned value is exactly `radix_value input mod feP`.
The full six-word/48-byte metadata readiness, owned private fields,
fresh-local separation, and unchanged input field are derived. A load-level
frame preserves every old location and permission: all writes so far are
to freshly allocated private locals. No initialized temporary, source
separation, helper execution, or post-state is added as a theorem premise.
The only memory premises are the represented input field and existing
modulus-global readiness; its limb bound is an internal input bound already
satisfied by public field readers and the arithmetic helpers' outputs.

The proof reuses the checked struct-copy, normalizer, signed62 conversion
and generic internal-function permission theorems. In particular, the
normalizer's Freeable ownership is derived from its real internal execution,
not inferred from a writable-only field predicate. No external library model
is introduced.

This prefix stops **before `secp256k1_modinv64_var`**. The core's actual
divstep execution/matrix correspondence, loop invariant and termination,
canonical inverse result, unpacking, complete wrapper composition and local
reclamation remain required. Existing core and affine suffix results do not
by themselves discharge that gap. This is not a registered `fe_invert` or
`gej_normalize` proof; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_fe_inv_prefix.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_fe_inv_prefix
```

## Original divstep post-count/exit slices (internal progress, no added coverage)

`jet_secp_div62_count.exec_div62_count_prefix` executes the original five
post-count assignments and the following break test for every internal
`0 <= zeros <= i <= 62`. It derives the exact shifted machine words, eta
subtraction and remaining counter, with unchanged memory and a temporary
frame outside the five assigned variables. Its outcome is `Out_break`
exactly when `zeros = i`. The separate `exec_div62_copy_count` covers the
original assignment from the helper-return temporary to `zeros`.

`jet_secp_div62_finish.exec_div62_finish` executes the original four signed
matrix-field stores and eta return, from any freeable 32-byte matrix storage;
its prior contents need not be initialized. All four stored words, continued
ownership and framing of other blocks are derived. The existing symbolic
executor is reused with an empty helper table and empty event log; there is
no helper execution or output premise.

`exec_div62_count_exit` composes the **exit slice** as two actual statement
executions: the original post-count loop remainder exits with `Out_break`,
and the original post-loop tail writes the shifted matrix words and returns
eta. A shared `exec_statement_prefix_aborts` lemma in
`jet_secp_statement_prefix.v` proves that the unexecuted tail is skipped for
any non-normal prefix outcome; it does not assume execution of that tail.
This slice does not assert that the whole enclosing loop or function has
executed, since the earlier count call and loop-head state are not supplied.

The count is an already-returned **internal temporary** in these results.
Neither the original CTZ call nor a model of its external builtin is proved
or postulated. The non-exit eta branches, their exact 32-bit `w` arithmetic,
the common cancellation updates, restoration of the delayed-division loop
invariant, and correspondence with `Trans.transN 62` remain required.
The existing VST proof's delayed-division invariant and pure `C.divstep` /
`C.modinv` lemmas can guide those steps, but its different checked AST and
internal de Bruijn CTZ routine are not substituted for the original target.
No public registration is added; coverage remains 514/533.

```sh
JET_TARGETS="C/jet_secp_div62_count.vo C/jet_secp_div62_finish.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_statement_prefix C.jet_secp_div62_count C.jet_secp_div62_finish
```

## Original divstep cancellation tails (internal progress, no added coverage)

`jet_secp_div62_cancel.exec_div62_cancel` executes both original cancellation
tails: the selected `w` computation, then `g += f*w`, `q += u*w`,
`r += v*w`, and the original no-op assertion loop. The statements are
extracted from the unchanged divstep body, with structural equalities
checked in Coq. The theorem derives all four assigned temporaries, preserves
every other temporary, and leaves memory exactly unchanged. The words and
mask are arbitrary; no divisibility or helper-execution premise is assumed.

The four-bit path retains the original truncation of its first `w` value
to uint32, uint32 negation, and zero-extension before multiplication. It is
not silently replaced by unbounded integer or 64-bit negation. The six-bit
path likewise retains its actual 64-bit arithmetic and uint32 result cast.

These are suffixes **after** branch selection, swaps, limit and mask
calculation. Their execution and the mathematical cancellation/matrix
correspondence still require composition with the delayed-division invariant.
This closes the exact-word execution obligation for the cancellation tail,
not the CTZ call, complete divstep loop, inversion, or any public jet.
No external model or public registration is added; coverage stays 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_cancel.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_cancel
```

## Original divstep limit/mask suffixes (internal progress, no added coverage)

`jet_secp_div62_limit.exec_div62_limit` executes the original conditional
limit selection, limit assignment, assertion no-op and mask calculation in
both eta branches. From the internal bounds `0 <= eta <= 745` and
`1 <= i <= 62`, it derives `limit = min(i, eta+1)`, the actual mask word,
all three assigned temporaries and unchanged memory. All other temporaries
are preserved. The long-to-int cast, signed comparison and arithmetic, and
unsigned-long shift guard are proved under these bounds; in particular the
shift count `64-limit` may be 63, not merely at most 62.

`exec_div62_after_swap` composes this execution with the original `w`
calculation. It takes the eta and words **after** the negative-eta swaps,
or unchanged for the nonnegative branch; it does not assume the mask or
execution of either suffix. Structural source equalities select the real
branch substatements, with their distinct generated conditional temporaries.

The preceding swaps/branch selection, derivation of these internal bounds
from the delayed-division loop invariant, the mathematical mask/cancellation
and transition-matrix bridges, CTZ call and complete inversion/public-jet
composition remain required. These internal-state bounds are not public
jet input exclusions or a newly accepted public theorem. Coverage remains
514/533, and no external-behavior model has been added.

```sh
JET_TARGETS=C/jet_secp_div62_limit.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_limit
```

## Original post-count non-exit execution (internal progress, no added coverage)

`jet_secp_div62_branch.exec_div62_count_nonexit` now composes the actual
post-count shifts, eta/counter subtraction, non-break test, no-op assertion
loops, eta sign branch, negative-eta swaps, limit/mask and `w` calculations,
and common `g/q/r` updates. It covers the whole original loop remainder
`div62_after_count` when `0 <= zeros < i <= 62` and the updated eta lies
in `[-745,745]`. Its computed final temporary environment includes the real
branch-local conditional temporary and the last swap temporary. Memory is
exactly unchanged. `div62_continued_temps_outside` separately frames every
temporary not assigned by the non-exit suffix. The source equalities and
execution lemmas refer to the unchanged original divstep AST throughout.

`exec_div62_nonexit` exposes the same suffix starting after the counter
update; `exec_div62_swap` proves the ten negative-eta assignments for
arbitrary machine words, and `exec_div62_eta_branch` derives which branch
executes from the signed eta comparison. These discharge the preceding
branch-selection/swap execution obligations of the earlier suffix lemmas.
The exit case is handled separately by `exec_div62_count_exit` above.

The returned count and eta bound are still **internal-state premises**.
The CTZ call/sentinel behavior, derivation and preservation of the
delayed-division invariant, correspondence with `Trans.transN 62`, outer
inverse-loop termination/result and complete public-jet composition remain
unproved. In particular, exact word execution alone is not a proof of the
mathematical inverse or a newly covered jet. No CTZ/memset model, public
assumption or registration is added, and coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_branch.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_branch
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

