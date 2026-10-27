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

## Scalar inverse conversion dependency (internal progress)

`jet_secp_scalar_signed62_numeric.eval_scalar_to62_value` proves the actual
`secp256k1_scalar_to_signed62` call for every four-word input in owned scalar
storage. The five returned signed62 words are canonically positioned and
have exactly the original 256-bit unsigned value. No scalar normalization
restriction or result/helper execution is assumed.

`eval_scalar_from62_value` proves the original reverse conversion for every
canonically positioned five-word signed62 input, returning four scalar
words with exactly the same unsigned value. Both calls retain the source
contents, input/output ownership and outside-block framing. Their distinct
owned regions match the private-signed62/caller-scalar layout of the inverse
helper; this is not a new public input/output disjointness contract.

The two conversion executions share one symbolic/storage interface in
`jet_secp_scalar_signed62.v`. Their arithmetic interpretation reuses the
field repacking bit-window lemmas, accounting for the 64/62-bit boundaries
and high bits discarded by individual word shifts. No C, AST, generation
setting, specification or external-call model is changed.

`jet_secp_scalar_inverse_caller.scalar_inv_entry_to_core` composes the real
inverse-helper entry, fresh 40-byte local allocation and original packing
call. It derives the exact packed value and position bounds, ownership,
separation, retained scalar input and evaluation of the actual core-call
arguments. Input and output scalars may be the same block, as they are in
the original public scalar-invert jet. The scalar-modulus symbol lookup is
proved; initialized contents of that global are not assumed or established
by this address-evaluation result.

`exec_scalar_inv_unpack_and_free` derives the original reverse conversion
and actual private-local reclamation from a live, canonically positioned
signed62 result. `scalar_inv_call_from_core` checks how the proven
entry/packing stages and that suffix compose into the complete helper call
when supplied the actual intervening core execution and its live result.
Those core premises remain unresolved; this call-context theorem is not a
public scalar-invert equivalence or a new library model.

These results do not discharge the complete `scalar_inverse_var` or public
`scalar_invert` proof.

`jet_secp_modinfo_scalar_global.modinfo_scalar_initial_state_exists` now
reuses the existing program-initialization existence theorem to establish
the actual scalar global's initial state: all 48 readable bytes and six
words, including the signed limb -21 and the low-limb inverse coefficient,
with readonly status. Closed identities check that its signed62 modulus is
the canonical scalar group order and its inverse coefficient is correct
modulo 2^62; the field modulus is not substituted.

`scalar_inv_entry_with_modinfo` composes that modulus state at caller entry
with the real allocation/packing prefix, deriving all six preserved global
words and their readability at the core-call boundary. There is no assumed
post-packing global state or load. Separation from the private scalar
regions is derived from freshness, readonly status and the existing owned
scalar contract, not added as a public input restriction. This does not
prove startup-state preservation through arbitrary earlier application
calls, or construct the scalar-specific inverse loop invariant.

Complete modular inversion and public caller/read/write composition remain open. In
particular, the field-modulus-specific inverse results cannot be reused as
scalar-order results without a proved modulus-general bridge. Coverage
remains 514/533; no new library premise is introduced by these helpers.

The normalization part of that bridge is now shared in
`jet_secp_modinv_normalize62_modulus.modnorm62_machine_numeric`. It derives
canonical signed62 words and the exact signed residue for modulus limbs
whose signed radix value is M, with proved per-limb bounds and
2^248 <= M <= 2^256. The existing field numeric lemmas keep their statements
and specialize this shared derivation; they are not repurposed as scalar
results.

`jet_secp_scalar_normalize62.eval_scalar_norm62_numeric` instantiates those
premises with the actual scalar global, derives its loads from global
readiness, and executes the original C `modinv64_normalize_62`. It proves
the canonical result modulo the scalar group order, ownership, framing and
preservation of all six modulus words. Its signed-limb/value bounds are
internal obligations still to be established by the scalar inverse loop.
There is no assumed normalize call, output fact, or new external model.
This completes normalization only, not inversion or public jet coverage.

`jet_secp_scalar_inverse_finish.exec_scalar_inv_finish_and_free` additionally
executes the original core's final sign load, normalization and signed62
copy-back, then frees its actual five local objects. The sign is loaded
from represented f storage, not supplied as an assumed temporary. The
result remains canonical in the caller's signed62 buffer with the exact
signed residue modulo the scalar order, ownership and the complete modulus
global preserved. The field and scalar cleanups reuse
`inv_free_env_blocks_structural`, which depends only on the actual local
environment, layout length and distinct allocated blocks; the original field
cleanup contract is unchanged.

This is a terminal-state suffix: its memory, signed-limb/value bounds, length
and local ownership must still be established by the actual inverse loop.
It does not assume an execution or a post-normalization output, but also
does not prove the complete core call or identify the terminal coefficient
with the frozen scalar inverse specification. Public scalar caller
composition and the deferred CTZ boundary remain open; coverage is unchanged.

`jet_secp_scalar_inverse_result.exec_scalar_inv_finish_literal` interprets
that same actual finishing execution against the frozen Haskell
`scalar_invert` program, not merely an abstract inverse. Its literal port in
`jet_secp_scalar_invert_literal.v` reuses the word-exact Bezout simulation,
proved EEA termination and existing literal scalar negation. The bridge
covers every 256-bit input, including zero and the word equal to the scalar
order. It retains the literal result for the original word before canonical
input reduction, and explicitly equates the recovered output word with the
literal Simplicity program's result. The needed scalar-order primality is checked with ordinary
Coq reduction from explicit certificate data; no unchecked example proof or
primality assumption is imported.

The terminal suffix requires the actual loop to establish its trajectory,
coefficient congruence, lower-limb bounds, stopped g and zero-case invariant.
Those are not established by the suffix theorem. Its C execution,
normalization, copy-back, frees, canonical output, ownership, global state
and framing are all derived from the stated internal memory/invariant
premises. This is not yet a whole core call, scalar-invert jet theorem or
new public proof entry. CTZ remains deferred and coverage stays 514/533.

`jet_secp_scalar_de_numeric.eval_scalar_de_value` now proves the actual
`modinv64_update_de_62` call with the six scalar modulus/metadata words.
For each matrix row it derives the exact integer equation
`2^62 * output = matrix_value + canonical_group_order * correction`, plus
the corresponding congruence, all ten actual output-word loads, representation
and framing. The complete call uses the existing verified 128-bit helper
table; its word recurrence is checked against the real C outputs using the
existing proved symbolic-expression comparator. It does not assume a
coefficient-update execution or output value.

The recurrence includes the scalar modulus's nonzero second limb and signed
third limb -21, as well as its distinct low-limb inverse coefficient. A shared
correction-mask lemma retains the original field contract as a specialization.
Scalar intermediate carries are treated as full signed-128 values, not
forced into the field proof's signed-64 carry bound; the last modulus limb
256 gives a separate tight bound proving that the final stored carry does
fit signed 64 bits. The scalar low-limb divisibility follows from the checked
actual inverse coefficient.

Matrix-row bounds and input-limb bounds are internal loop premises here.
Scalar loop-state composition and whole
loop/caller composition remain required before
public acceptance. CTZ remains deferred; no new external model, target change
or public proof entry is added, and coverage remains 514/533.

`jet_secp_scalar_de_revalue.eval_scalar_de_step` derives the complete next
coefficient-update representation from that real call, retaining the original
matrix, scalar modulus metadata, ownership and memory frame. The output's
value range (-2*N,N) and signed62 limb bounds are now proved preserved by
`jet_secp_scalar_de_ranges`, not assumed as postconditions. Its balancing
argument specializes the existing modulus-general normalization proof;
the field and scalar cases share `de62_balanced_row_modulus`. All original
field contracts are retained. The input bounds and represented initial state
remain internal loop premises to be established by the actual caller; this
state-transformer result is not a complete inverse-loop or public jet proof.

`jet_secp_scalar_de_invariant.eval_scalar_de_invariant` connects the actual
coefficient call to the canonical `stepN 62` state: it derives matrix-row
bounds from the incoming canonical matrix relation, preserves the input's
coefficient congruence, and proves that d modulo the scalar order stays
unchanged when incoming g is zero. The zero-case fact is separate because
the coefficient congruence alone says nothing about d when the input is
zero. Its modular algebra is shared with the field case through
modulus-general cancellation, linear-combination and scaled-coefficient
lemmas; the original field contracts remain unchanged. The actual loop
must still establish the initial representation/bounds, coefficient link
and canonical matrix relation, and execute/update its f/g state before this
component can form a full inverse iteration. No CTZ model or public coverage
entry is added.

`jet_secp_scalar_inverse_seed.scalar_inv_entry_establishes_seed` now derives
the initial scalar state from the actual `scalar_inverse_var` entry and
packing, then the real `modinv64_var` allocation and all fourteen pre-loop
statements. The five local objects are fresh; d=0, e=1, f=the actual scalar
modulus and g=the packed input are established by actual memory loads.
It derives len=5, eta=-1, the initial coefficient link, coefficient/limb
bounds, canonical initial f/g values and bounds, and the separate d=0
residue fact. The transition matrix is correctly still uninitialized: no
matrix or divstep-call result is assumed. The shared modules
`jet_secp_modinv_entry_modulus` and `jet_secp_modinv_copies_modulus` handle
arbitrary six-word metadata; their field specializations are definitionally
the existing field representations. They reuse the original statement and
allocation layout, checked signed62 By_copy execution, copy-argument,
representation-preservation and loop-setup proofs. No libc copy premise is
needed. The scalar loop must still produce its canonical matrix and compose
the represented updates, stopping/shortening control and iteration/termination
with the checked finishing path. CTZ remains deferred, and public coverage
remains 514/533.

`jet_secp_scalar_inverse_updates.exec_scalar_inv_updates_invariant` now
executes the actual coefficient-update and f/g-update call pair in the
original caller's one represented seven-object layout. It derives both
calls, the complete updated representation and ownership, the scalar
coefficient bounds and exact correction equations, lower f/g limb bounds,
framing, coefficient congruence and the canonical `stepN 62` f/g state.
The separate zero-case d residue is preserved. The modulus-independent
f/g call and caller restoration are reused through
`jet_secp_modinv_loop_modulus`, which retains arbitrary six-word metadata
and specializes definitionally to the original field layout. Scalar d/e
values are proved unchanged by the subsequent f/g call; f/g inputs and
matrix are proved unchanged by the preceding coefficient call. Incoming
matrix correspondence and numeric limb/state invariants are internal loop
premises, not assumed C executions or post-update results. Actual divsteps
must establish that correspondence. Full-loop/finishing composition remains
a separate obligation; this is not a full inverse or new public jet proof.

`jet_secp_scalar_inverse_iteration.exec_scalar_inv_after_divsteps` now
composes that call pair with the original zero test and shortening control.
It derives the complete represented next state, actual next len, unchanged
coefficient values through shortening, scalar bounds/congruence, canonical
next f/g values, lower-limb bounds, caller temporary frame and memory frame.
Break is equivalent to the represented next g being zero; continuing implies
nonzero g. If incoming canonical g is already zero, it derives the actual
break and preserves d modulo the scalar order. No stop/shortening execution
or expected result is a premise.

The shared `jet_secp_modinv_control_storage` proves the real shortening
stores from initial loads and permissions and composes the existing
load-based zero test and condition-prefix proofs, including the early-break
path. `jet_secp_modinv_tail_modulus` restores arbitrary six-word metadata,
the complete seven-object caller layout and its ownership, and the pure
existing numeric control model.
Both arrays' loads and permissions are kept across the other's store; the
metadata and coefficient arrays are preserved by the derived frame, not by
assuming field-modulus words in scalar memory. Actual divsteps/matrix
correspondence and whole-loop/finishing composition are still open. CTZ remains deferred;
coverage remains 514/533, with no target or external-model change.

The post-divstep theorem additionally derives bounds for all five stored
f/g limbs (including inactive slots) and the adjusted active-value capacity
from the incoming capacity invariant. It reuses the canonical `fgBounds`,
actual f/g-update range lemma and shared shortening range theorem. No
post-update bound or extra execution premise is assumed. All earlier
conclusions and incoming premises are retained.

`jet_secp_modinv_seed_modulus` revalues the actual initialized/copy-complete
memory into the corresponding full input/d/e/f/g word dictionary while
retaining the undefined matrix region. The existing field dictionary and
layout are definitionally its field specialization. The strengthened
`scalar_inv_entry_establishes_seed` derives this represented state from the
real caller, together with initial scalar coefficient bounds/congruence,
canonical f/g correspondence, all stored f/g limb bounds and the len=5
capacity invariant. The scalar modulus's signed third limb is -21; no
nonnegative-modulus-limb assumption is imposed. The initial capacity follows
from the already proved 256-bit value bounds. These invariants are now
established at initialization and preserved by the real post-divstep path,
not left as output assumptions. The earlier divstep/matrix proof and the
whole inverse loop/finishing composition remain separate work.

```sh
JET_TARGETS="C/jet_secp_scalar_signed62.vo C/jet_secp_scalar_signed62_numeric.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_signed62 C.jet_secp_scalar_signed62_numeric
JET_TARGETS=C/jet_secp_scalar_inverse_caller.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_inverse_caller
JET_TARGETS=C/jet_secp_modinfo_scalar_global.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinfo_scalar_global
JET_TARGETS="C/jet_secp_modinv_normalize62_modulus.vo C/jet_secp_modinv_normalize62_numeric.vo C/jet_secp_scalar_normalize62.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinv_normalize62_numeric C.jet_secp_scalar_normalize62
JET_TARGETS="C/jet_secp_scalar_inverse_finish.vo C/jet_secp_modinv_var_result.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_inverse_finish C.jet_secp_modinv_var_result
JET_TARGETS="C/jet_secp_scalar_prime.vo C/jet_secp_scalar_invert_literal.vo C/jet_secp_scalar_inverse_result.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_prime C.jet_secp_scalar_invert_literal C.jet_secp_scalar_inverse_result
JET_TARGETS="C/jet_secp_scalar_de_exec.vo C/jet_secp_scalar_de_recurrence.vo C/jet_secp_scalar_de_numeric.vo C/jet_secp_scalar_inverse_result.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_recurrence C.jet_secp_scalar_de_numeric C.jet_secp_scalar_inverse_result
JET_TARGETS="C/jet_secp_scalar_de_ranges.vo C/jet_secp_scalar_de_revalue.vo C/jet_secp_scalar_inverse_result.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_revalue C.jet_secp_scalar_inverse_result
JET_TARGETS="C/jet_secp_scalar_de_invariant.vo C/jet_secp_modinv_var_result.vo C/jet_secp_scalar_inverse_result.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_de_invariant C.jet_secp_modinv_var_result C.jet_secp_scalar_inverse_result
JET_TARGETS="C/jet_secp_modinv_entry_modulus.vo C/jet_secp_modinv_copies_modulus.vo C/jet_secp_scalar_inverse_seed.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_copies_modulus C.jet_secp_scalar_inverse_seed
JET_TARGETS="C/jet_secp_modinv_loop_modulus.vo C/jet_secp_scalar_inverse_updates.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_loop_modulus C.jet_secp_scalar_inverse_updates
JET_TARGETS="C/jet_secp_modinv_control_storage.vo C/jet_secp_modinv_tail_modulus.vo C/jet_secp_scalar_inverse_iteration.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_control_storage C.jet_secp_modinv_tail_modulus C.jet_secp_scalar_inverse_iteration
JET_TARGETS="C/jet_secp_modinv_seed_modulus.vo C/jet_secp_scalar_inverse_seed.vo C/jet_secp_scalar_inverse_iteration.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_seed_modulus C.jet_secp_scalar_inverse_seed C.jet_secp_scalar_inverse_iteration
```

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

`jet_secp_wnaf_function15.eval_wnaf_literal15_from_memset_step` now composes
the entire original 129/15 helper conditional on that single original
`memset` statement's execution, its zero loads and its unchanged-permission /
outside-output frame effects. The actual allocation, eight preparation
statements, scalar copy, sign selection, literal-aware loop, return conversion
and private-local free are derived, not assumed. For every Word128 scalar
(the generator's split halves), the final owned array equals the decoded
literal vector, and the actual return length removes only leading zero
digits. All old memory outside the output block and the source scalar survive
cleanup. Input/output block separation is the internal generator layout, not
a new restriction on public frame layouts.
The strengthened endpoint also retains exact permissions on every pre-existing
block, in both directions, despite allocating and freeing the private scalar.

The allocation equation identifies the actual entry allocation; the only
assumed execution is the exact original external-call statement, not the
wNAF helper, a loop iteration or a mathematical replacement. This does not
discharge or define `memset`, connect both calls through Strauss, or prove
the public `generate` jet. Coverage remains 514/533. Reproduce its build and
kernel check with the commands below using
`C/jet_secp_wnaf_function15.vo` / `C.jet_secp_wnaf_function15`; inspect its
reviewed assumption/contract snapshots for the precise conditional boundary.

`jet_secp_generator_wnaf_setup.exec_generator_wnaf_setup` composes both
actual caller statements: the low-half call through `_t'6` to `_bits_ng_1`,
the high-half call through `_t'7` to `_bits_ng_128`, and the original two
maximum-count updates. It derives the two literal digit arrays, destination
ownership, exact maximum return length, unchanged other temporaries, external
memory framing and exact permissions on old blocks. The first array and the
second scalar survive the intervening calls. Both read-only generator tables
are preserved from their initial represented state; that preservation is not
assumed as a postcondition. Local-array separation matches the actual distinct
Strauss allocations. Every Word128 half is covered, including zero.

The explicit premise supplies only the exact original zeroing statements for
the two call slots in owned destinations. The wNAF calls, their scalar copies,
literal results, return assignments and cleanup are proved using the preceding
function theorem. This introduces no axiom or replacement external semantics.
It does not discharge the deferred zeroing steps or compose Strauss entry,
scalar splitting, the point stage, final local frees and public read/write
into the public `generate` theorem. Coverage is unchanged. Build/check the new
module with the same commands using `C/jet_secp_generator_wnaf_setup.vo` /
`C.jet_secp_generator_wnaf_setup`.

`jet_secp_generator_function.eval_generator_strauss_from_owned` now composes
the whole original Strauss helper on the actual `num=1`, zero auxiliary-scalar
path. Its arbitrary logical Word256 input is not fixed to zero: the internal
scalar storage contains the reader's canonical normalization for that input.
Actual entry allocates nine distinct locals; preparation derives Z=1 and
preserves initially read-only globals, so both table states are established
at the main stage from their state before entry, not assumed after a prefix.
The guarded scalar split, both original wNAF calls, maximum lengths, infinity
setup, descending point loop and final Z correction execute. The theorem then
frees all nine actual locals and returns the exact point fields, infinity
flag, coordinate bounds, retained input/output ownership and old-memory frame.

The result is the complete literal `generate` tree in
`jet_secp_generate_program.v`, assembled in the canonical Haskell order from
the already-proved scalar-split, wNAF and step129 ports (LibSecp256k1.hs:
614--627,792). The literal port and its parametricity are proof support, not
edits to the frozen specification. `jet_secp_generator_main` is the checked
branch-through-point-stage composition used by that whole-call result.

The only assumed executions are the exact original `memset` statements with
their zero loads and memory effects on valid owned destinations. No wNAF,
split, table lookup, point-loop iteration or helper return is assumed. This
remains conditional internal progress: the enclosing `secp256k1_ecmult`
allocations/state setup are composed by the subsequent result below; public
`simplicity_generate` composition is proved by the later result below;
zeroing remains outstanding.
No public jet is registered, and coverage stays 514/533. Reproduce the build
and recursive kernel check with the commands below using
`C/jet_secp_generator_function.vo` / `C.jet_secp_generator_function`.
The literal port is closed. The main-stage and whole-helper results inherit
the eight assumptions already recorded for `exec_generator_point_stage` /
`exec_generator_loop`, including CompCert's generic external-call and
inline-assembly properties. They are not six-assumption results like the
wNAF-only endpoints. The strengthened initialization/entry proofs add no
assumptions to their existing sets; no new axiom or library model is declared.

`jet_secp_ecmult_generator.eval_ecmult_generator` further composes the actual
enclosing `secp256k1_ecmult` call on this path: its four allocations (320,
704, 1040 and 24 bytes), three pointer stores into the Strauss state, original
Strauss call, void return and all four local frees. It derives the same
literal point, bounds, infinity flag, retained scalar/output ownership and
old-memory framing. No point representation is required for the unused
auxiliary point when the actual static auxiliary scalar is zero.
It reuses the existing `jet_secp_ecmult_entry` and `jet_secp_ecmult_state`
proofs of those layouts and stores against the existing AST, rather than a
second setup proof. `jet_secp_generator_startup` establishes the actual zero
scalar and both read-only generator tables from `Genv.init_mem`, and transports that state
through allocation, stores, calls and frees. In particular, startup readiness
is retained by the enclosing ecmult call rather than assumed afterward.

This result is still conditional on exactly the original wNAF `memset` steps,
with their zero loads and memory effects, and inherits the same eight
assumptions as the Strauss result. It neither introduces a replacement
external-call model nor changes the C, AST or specification. The public
composition is completed by the subsequent result below. Coverage remains
514/533. Reproduce
the normal build and recursive kernel check with the same commands using
`C/jet_secp_ecmult_generator.vo` / `C.jet_secp_ecmult_generator`.

`jet_secp_generate_lifecycle.eval_generate_initialized` now executes the
complete original public `simplicity_generate` function against the literal
Simplicity `generate` specification, on arbitrary valid frames/cursors
and every Word256 input. It derives all three allocations, actual by-value
source copy, scalar read and canonical normalization, the original ecmult
call with the real static auxiliary arguments, point serialization, true
return, and all three local frees. The postcondition includes output bits,
the output prefix/cursor and load framing supplied by `finv`, old-memory
framing, and retained startup state. No scalar nonzero, curve-membership,
special cursor, zero-initialized output or input/global-separation premise
is introduced. The entry/body modules reuse the existing scalar reader,
allocation, copy, literal-point writer and readonly-preservation lemmas.

`jet_secp_generate_local.generate_initialized_local_spec_from_memset_steps`
exports exactly the existing `secp_jet_initialized_local_spec`, conditional
only on the unchanged original zeroing-step parameter. In the same module,
`generate_runs_from_actual_init` constructs a valid input/output frame pair
for every Word256 value starting from `Genv.init_mem jets_secp.prog`, invokes
the whole public function and preserves the initially existing memory loads
and startup state. `generate_startup_old_blocks` proves that frame construction
preserves the actual initialized globals, recovering their readability from
preserved byte loads rather than assuming it.

The public call, local contract and fresh-frame result inherit the same eight
assumptions as the whole Strauss/ecmult chain. The sole deferred execution
parameter still supplies the exact original wNAF `memset` statements, their
129 zero words and memory effects in valid owned destinations. It does not
assume any internal or public jet execution or specification result. There
is no new axiom, external-call model or coverage row: coverage stays 514/533.
Reproduce the normal build and recursive kernel check with the same commands
using `C/jet_secp_generate_local.vo` / `C.jet_secp_generate_local`.

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

### Canonical serialization after inversion (internal progress)

`jet_secp_gej_norm_output.exec_affine_normalized_output` composes that actual
affine suffix and its temporary reclamation with the original `write_ge`.
Starting after inversion and after the leading finite tag has been written,
it derives the final frame invariant for
`[Some true] ++ encode (literal_gej_norm ((a,b),c))`. The tag, prefix, cursor
update and output-frame framing are retained by the existing writer invariant.
Caller-owned point storage remains Freeable; unrelated memory outside the
four owned blocks and external frames is preserved by the composed memory
frame. The intermediate output fields, their bounds, cleanup and writer
execution are derived from the unchanged C helpers, not execution premises.

`affine_normalized_words_literal` proves the numeric-to-literal word bridge
from the suffix's two modular coordinate equations and input correspondence.
The crucial remaining internal premise is explicit:
`radix_value zi mod feP = literal_invert_numeric (toZ c) mod feP`.
It is not asserted for an arbitrary incoming field and is not added to a
public jet contract. Whole inversion must establish it before this result
can be used in an accepted `gej_normalize` proof. Function entry, preceding
inversion/CTZ execution, actual finite-tag write and the other public branch
and caller-frame obligations remain open. No new external model, target
change or public registration is made; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_gej_norm_output.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_norm_output
```

### Original normalization caller: test/tag and complete infinity branch

`jet_secp_gej_norm_branch.exec_gej_norm_header` executes the real flag
accessor followed by the caller's boolean negation, `writeBit` call and return
temporary. Both flag values are covered. The exact original public statement
tree is retained by `gej_norm_body_source`. The new `literal_gej_normalize`
adapter translates the unchanged canonical Haskell `gej_normalize` at
`Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:554`; its value equation and
parametricity are proved, rather than substituting a numeric specification.

`jet_secp_gej_norm_infinity.gej_normalize_infinity_literal_local_spec` proves
the complete original public C call when the canonical Z-zero predicate is
true. It derives all three caller allocations, the by-value frame copy,
actual canonical XYZ reads and stored flag, test/tag, original `skip_ge`
padding, successful return and freeing all caller locals. The result is the
literal Simplicity output with the usual prefix, cursor and outside-memory
guarantees for arbitrary valid physical cursors and initial output contents.
The padding cells remain unconstrained; no zero-initialization is required.
The source frame, owned storage and freshness facts are derived, not assumed
post-read or as execution premises. Generic allocation properties are reused.

This is explicitly a **restricted branch theorem**, not a new full-jet
registration. Its canonical-infinity premise is retained in its statement;
all finite inputs still require proof. The preceding post-inversion canonical
output bridge and the caller header can be reused there, but complete
inversion/CTZ execution, finite branch composition and cleanup remain open.
No external-library premise, implementation/specification change or coverage
credit is added. Accepted coverage stays 514/533.

```sh
JET_TARGETS=C/jet_secp_gej_norm_infinity.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_norm_infinity
```

### Finite caller data and nested inverse preparation (internal progress)

`jet_secp_gej_norm_reads.exec_gej_norm_read_and_tag` composes the original
`read_gej` and caller header for both canonical flag values. It reuses the
existing stronger coordinate reader and limb bridge, returning the actual
normalized X/Y/Z fields after the tag write, the unchanged stored flag,
advanced source cursor, ownership of all caller locals and the tagged frame
invariant. No coordinate load, flag, output or helper execution is assumed
after reading. `affine_inverse_reader_value` identifies the inverse
preparation's input value with the original Z word modulo the field prime.

`jet_secp_gej_affine_entry.affine_entry_to_inverse_core` derives actual entry
into `secp256k1_ge_set_gej_var`, its finite-flag guard, evaluation of both
Z-at-offset-80 arguments, entry into `fe_inv_var`, and its real
copy/normalize/signed62-pack preparation. It reuses `fe_inv_entry_to_core`;
the input's packed representation, normalization, numeric value, owned
storage and fresh local blocks are derived. All pre-existing caller loads
and permissions are framed through these steps, retaining the computed tag
when the frame invariant is transported across them. The exact original
function-body context is checked by `affine_entry_source`.

`jet_secp_modinfo_fe_caller.modinfo_fe_state_initial` obtains the modulus
representation and readonly status from the actual program initialization.
`read_gej_preserves_modinfo` proves preservation through the real reader's
closed internal call graph. For the tag/header, `frame_write_keeps_modinfo`
derives that the readonly modulus block cannot be either writable frame
block, then applies the existing load/permission frame. It does not assume
behavior for the unreachable assertion call in the AST.
No input/global disjointness condition or external-library premise is added.

`gej_norm_finite_enters_inverse` composes these facts with both prefixes:
modulus state is required before reading, not assumed afterwards. From input
cells and the existing caller/frame ownership it derives the read/tag,
both nested function entries, the finite guard and original inverse
preparation, retaining X/Y/Z, the tag, all seven local allocations, global
metadata and outside framing. The packed input's exact numeric value is
the original Z word modulo the field prime.

`jet_secp_gej_norm_infinity.gej_norm_prepare` factors the actual public
function entry and by-value source-frame copy out of the complete infinity
proof, which now reuses it. Fresh caller allocations, their ownership and
separation, the local source fields and initial frame invariant are all
derived. Modulus state is transported through those allocations and the
copy without external-call properties or a new library premise.

`gej_normalize_finite_public_prefix` then starts from the ordinary public
source/output frames, input cells and modulus state at call entry, rather
than assumed private locals. It composes that real entry/copy with the
read/tag and nested inverse preparation, returning the same exact packed
input and caller fields/ownership, plus framing relative to the initial
public memory. No intermediate readiness or helper execution is assumed.
Initialization of the modulus state remains `modinfo_fe_state_initial`;
this result does not establish its preservation through arbitrary earlier
application calls.

These are execution/representation prefixes, not a full nested call or a
finite public-jet equivalence. Complete modular inversion,
its canonical inverse correspondence, finite suffix/call/return composition
and public cleanup remain required.

`jet_secp_signed62_slice.eval_fe_repack_to_slice` now executes both original
field/signed62 conversions with an arbitrary aligned destination slice.
The original symbolic expressions and numeric bridges are reused. Slice
regions no longer pretend to be whole allocations; preservation of all old
permissions is derived from the actual closed internal helper execution.
Framing is byte-range-sensitive, including elsewhere in the output block.

`jet_secp_fe_inv_finish.exec_fe_inv_unpack_slice_and_free` composes this
original conversion call with reclamation of the inverse helper's actual
two locals. The old base-zero result is a specialization with its unchanged
contract. `exec_fe_inv_unpack_point_and_free` supplies the Z-at-80 case:
X/Y and the full 128-byte point ownership survive, the output's bounds and
exact value are derived from the canonical signed62 input, and only bytes
80--119 of the point may change. This closes the earlier slice-interface
gap, not the modular-inverse execution: the canonical signed62 inverse
result must still be produced by that call before this suffix applies.

`jet_secp_gej_norm_output.exec_inverse_return_normalized_output` immediately
composes that real Z unpack/free with the checked affine arithmetic, affine
temporary reclamation and original `write_ge`. It derives the exact literal
finite normalization encoding and preserves the tag and remaining caller
ownership. The inverse loop's canonical signed62 output, its inverse-value
equality and surviving caller invariant remain explicit internal boundary
conditions; this is not an all-input public jet proof or coverage entry.

No new external model, axiom, target
change or coverage credit: accepted coverage remains 514/533.

```sh
JET_TARGETS="C/jet_secp_gej_norm_infinity.vo C/jet_secp_gej_norm_reads.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_norm_infinity C.jet_secp_gej_norm_reads
JET_TARGETS="C/jet_secp_signed62_slice.vo C/jet_secp_fe_inv_finish.vo C/jet_secp_gej_norm_output.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_signed62_slice C.jet_secp_fe_inv_finish C.jet_secp_gej_norm_output
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

## Original cancellation arithmetic bridge (internal progress, no added coverage)

`jet_secp_div62_numeric.div62_cancellation` proves that the cancellation
words used by the original execution have their intended bounded integer
value: with `k = min(limit,6)` in the swap branch or `min(limit,4)` in the
other branch, the actual uint32 result is exactly
`(modInv(-f,2^k) * g) mod 2^k`. It is below `2^k`, the integer `g+f*w` is
divisible by `2^k`, and the actual updated 64-bit `g` word masked by the
actual mask is zero. This holds for arbitrary integer representatives of
the machine words, assuming odd `f` and the internal eta/counter bounds.

The proof derives the mask as the low-`k`-bit mask, retains all original
64-bit wraparound and the four-bit path's uint32 cast/negation/widening,
and reuses `HackersDelightA/B` from `C.modinv`. Reduction of the inverse
formulas to a smaller cancellation width is proved, not assumed. These
lemmas bridge the concrete word expressions executed in the preceding
modules to the coefficient in `Trans.transSs`/`Trans.transDs`; they do not
substitute a pure algorithm for the C execution.

Still required are the transition-matrix/delayed-division invariant bridge,
derivation of oddness/count/bounds at each actual loop head, CTZ semantics,
outer-loop termination/result and public-jet composition. No external model,
new public premise or registration is added; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_numeric.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_numeric
```

## Original non-exit transition/invariant bridge (internal progress, no added coverage)

`jet_secp_div62_transition.exec_div62_transition_matrix` composes the
original non-exit execution with the canonical divstep matrix. It derives
an actual `Clight2.exec_stmt` with unchanged memory, and the pending
representation of `Trans.mul (Trans.transN k state) old_matrix` in the
resulting C temporaries. The first matrix row remains divided by `2^k`
until the next count/shift; the second row is already the canonical new
row. Eta equals the canonical state eta after `k` steps **plus `k`**, and
the remaining C counter is unchanged by cancellation. The proof does not
prematurely identify these temporaries with a fully divided state.

The same execution theorem derives `div62_pending_fg`: its first C word
approximates the new state's `f` modulo `2^(precision-k)` and its second
word represents `g_approx * 2^k`, with `g_approx` approximating the new
state's `g` at that precision. Both divisions are justified by the concrete
cancellation result. The low-bit precision can exceed `k`; exact equality
of the C input words with the large mathematical state is not required.
Oddness of the needed approximate operand is derived from congruence with
the canonical odd operand, not added as another premise.

`div62_positive_transition` / `div62_negative_transition` use the actual
computed uint32 coefficient in `Trans.transSs` / `Trans.transDs`. Their
canonical matrix and eta conclusions, and the modular quotient/precision
lemmas, discharge the mathematics used by the execution theorem. Existing
`Trans.transN_stepN` composes this new matrix on the left with a preceding
trajectory; no alternative implementation or checked AST is substituted.

The theorem starts **after the count assignments/test**, at a non-exit
internal state. Its premises remain the represented four old matrix words,
represented `f/g`, their low-bit approximation, the internal eta/counter
bounds, odd canonical `g`, and enough precision for this batch. It does not
assume a helper call, an execution, a resulting matrix, or a resulting
representation. Deriving those premises at entry and after each actual CTZ
call, preserving the full enclosing loop invariant and termination, and
composing the entire inverse/public jet remain required. No new external
model or public registration is added; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_transition.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_transition
```

## Original count/shift invariant restoration (internal progress, no added coverage)

`jet_secp_div62_consume.exec_div62_consume` executes the original count/shift
prefix, including its break test, from the pending matrix and `f/g`
representations established by cancellation. It derives the unscaled matrix
`Trans.mul (Trans.transN (zeros-pending) state) old_matrix`, new modular
`f/g` approximations, canonical eta, reduced counter and unchanged memory.
If it does not exit, the new canonical `g` is proved odd. Matrix scaling,
word truncation and precision loss are derived rather than assumed as
postconditions. The internal precision bounds include the 62-bit initial
precision case as well as a 64-bit one.

The pure sentinel lemmas prove properties of the **exact word expression**
passed to the counting helper: nonzero input, count in `[0,i]`, low-bit
divisibility, consumption of all pending zero bits, and the first remaining
bit being set unless the counter is exhausted. `div62_sentinel_source`
identifies that argument in the unchanged original loop, and
`eval_div62_sentinel` proves its actual Clight expression evaluation.
These results reuse `C.extraMath.Z_ctz`; they do not replace or prove the
production CTZ builtin.

**Unresolved boundary:** the execution theorem starts with the internal
`zeros` temporary equal to `div62_expected_count` of the represented `g`
and counter. That is an input-state relation, not an assertion that the
actual helper call establishes it. Its non-exit/exit outcome is derived
from that value. No external call, library-behavior model or helper
execution is postulated or added to public coverage. Establishing this
relation from the real abstract external builtin, original function entry,
full-loop composition/termination and the public inverse proof remain
required. Coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_consume.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_consume
```

## Original divstep entry invariant (internal progress, no added coverage)

`jet_secp_div62_entry.div62_entry_to_loop` proves the real
`function_entry2` and original seven initializer assignments for
`secp256k1_modinv64_divsteps_62_var`. No locals are allocated, and memory
is exactly unchanged. From low-bit congruence of the supplied words with
the canonical state's `f/g`, it derives `div62_pending_matrix` for the
identity matrix with zero pending division, `div62_pending_fg` at the
given precision, the original eta, counter 62, and unchanged output pointer.
Both 62-bit and 64-bit initial precision are covered. No initialized loop
temporaries or invariant are assumed as extra input premises.

This is entry **up to the loop**, not execution of that loop. The actual
CTZ call's return-value relation, full-loop composition/termination, final
matrix/specification connection and public inverse composition remain
unresolved. The preceding count and cancellation results do not themselves
establish the missing CTZ behavior. No external model or public theorem
registration is added; coverage stays 514/533.

```sh
JET_TARGETS=C/jet_secp_div62_entry.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_entry
```

## Original trajectory-indexed post-count invariant (internal progress, no added coverage)

`jet_secp_div62_invariant.exec_div62_postcount_invariant` composes the
original count/shift, break test and cancellation paths into one actual
execution of `div62_after_count`. Its invariant uses the canonical state
and matrix after `n` divsteps, the pending division, remaining precision,
actual eta/counter temporaries, and unchanged output pointer. The entry
corollary derives this invariant at `n=0` from the real function entry and
initializers.

The post-count theorem derives either an actual break with the canonical
62-step invariant and no pending division, or an actual normal return with
the same invariant at a strictly greater `n <= 62`. Thus the progress bound
is on canonical divsteps, not the C counter alone (which cancellation does
not decrement). Eta bounds at the cancellation point are derived from the
initial `[-683,683)` bound and `etaBounds`, not supplied as an extra
intermediate assumption. Both 62- and 64-bit initial precision are covered.

`jet_clight_temp_frame.exec_temp_frame` supplies reusable framing for
call-free, temporary-only statements. A conservative syntax check rejects
calls, stores and other unsupported statements. Closed checks on the actual
count and cancellation statements establish that they do not assign the
output pointer. Its preservation is derived from their real executions.

This theorem still starts **after the counting helper returns**, with
`zeros` equal to the expected mathematical count. It does not assume an
execution, resulting invariant or progress fact, but also does not prove
that the actual abstract CTZ builtin establishes that input-state relation.
The full enclosing loop/function and public inverse proof remain unfinished;
strict per-step progress does not by itself prove actual CTZ termination or
full-function execution. No external model or public registration is added;
coverage remains 514/533.

```sh
JET_TARGETS="C/jet_clight_temp_frame.vo C/jet_secp_div62_invariant.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_clight_temp_frame C.jet_secp_div62_invariant
```

## Canonical matrix stores and eta return (internal progress, no added coverage)

`jet_secp_div62_exit.exec_div62_exit` executes the original four final
matrix stores and eta return from the terminal 62-step invariant. Each
stored word's **signed value** is exactly the corresponding coefficient
of `Trans.transN 62 start`, and the returned word's signed value is the
canonical final eta. The coefficient ranges are derived from
`Trans.bounded_transN`, and eta's range from `etaBounds`; no signed-value
or representability premise is added for those outputs. Freeable ownership
of the 32-byte matrix is retained, and other memory blocks are framed.

The theorem reuses `exec_div62_finish` on the unchanged original stores.
It starts with the terminal invariant, so it does not claim that the
enclosing loop has executed or the CTZ builtin has returned the expected
counts. Together with the entry and post-count results this supplies the
canonical end-state/store boundary; actual full-loop/function execution,
the CTZ dependency and public inverse composition remain unfinished.
Coverage stays 514/533, with no new external model or public registration.

```sh
JET_TARGETS=C/jet_secp_div62_exit.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_exit
```

## Original field-inversion unpack and local reclamation (internal progress)

`jet_secp_fe_inv_finish.exec_fe_inv_unpack_and_free` executes the original
`fe_inv_var` unpack call, reusing `eval_fe_from_signed62_value`, and frees
the caller's actual two local objects in `blocks_of_env` order. It derives
the represented output limbs, their bounds and exact integer value, retains
the caller output's Freeable ownership, and frames blocks outside the output
and the two reclaimed locals. The helper call is proved, not assumed.

This suffix starts with a canonical signed62 result already in the local
`s` object and a separate owned base-zero 40-byte output, as used for a
caller's local field value. It neither assumes nor proves that the preceding
modular-inverse call has run correctly. Arbitrary output slices, the missing
inverse execution/value result and public jet composition remain open.
No external model, target change or public registration is added; coverage
remains 514/533.

```sh
JET_TARGETS=C/jet_secp_fe_inv_finish.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_fe_inv_finish
```

## Derive inverse matrix row bounds (internal strengthening, no added coverage)

`jet_secp_modinv_var_invariant.inv_matrix_row_bounds` derives both coefficient
row bounds directly from `inv_matrix_matches` and `Trans.bounded_transN`.
`inv_fg_bounds_from_matrix` supplies those same bounds for the f/g update's
projected matrix. `exec_inv_after_divsteps_invariant` now uses these results
internally instead of requiring matrix row bounds either as a separate
caller premise or as part of `fg_input_bounds`: only its f/g limb-bound
component remains a premise. All previous execution, representation,
coefficient/state, range and framing conclusions are retained. This is an
assumption-free arithmetic bridge to the original update executions, not an
assumption that divsteps ran correctly.

The matrix-match fact, f/g machine bounds, initial coefficient/state relation,
actual divstep execution, CTZ boundary and public inverse composition still
need to be discharged along the full call path. No new external model or
public registration is introduced; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_modinv_var_invariant.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_invariant
```

## Establish the inverse invariant from actual entry (internal progress)

`jet_secp_modinv_var_seed.inv_entry_establishes_invariant` reuses the original
`modinv64_var` entry, initialization, f/g struct copies and len/eta setup.
It derives a current-memory representation with the initialized coefficients
`d=0,e=1`, sparse modulus `f`, input `g`, `len=5` and `eta=-1`, together with
the coefficient link and canonical divstep-state match. It also establishes
the coefficient bounds, f/g limb bounds and initial 256-bit state bounds.
Ownership, the actual local environment, temporary matches, allocation
freshness and the prefix's memory frame are retained.

The 32-byte transition matrix is still explicitly uninitialized in
`inv_seed_regs`; no matrix result or execution is assumed. The input premise
is the canonical signed62 representation already produced by the checked
field-inversion pack step. Zero input is included, and no below-modulus
restriction is added to this internal prefix theorem. This does not establish
the divstep call, the outer loop or the final inverse value, and adds no
public coverage or external model. Coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_modinv_var_seed.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_seed
```

## First inverse batch: caller arguments and callee entry (internal progress)

`jet_secp_modinv_var_first_batch.inv_first_batch_setup` derives the actual
first f/g low-word loads from `inv_seed_regs`, evaluates the original
divstep-call arguments, and establishes the callee's real function entry,
seven initializer statements and initial `div62_loop_invariant` at 62-bit
precision. Its modulus/input low-bit correspondence is proved, not assumed;
the low-word casts retain the original bit patterns. The caller owns the
32-byte matrix buffer even though its cells remain uninitialized here.
`inv_divstep_statement_source` identifies these loads and call in the
unchanged caller statement tree.

This theorem composes setup boundaries, not a full `eval_funcall` of the
batch: the CTZ call, batch loop, matrix stores/return through the caller,
outer inverse loop and public jet composition remain unfinished. No extra
external model, target change or public registration is introduced.
Coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_modinv_var_first_batch.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_first_batch
```

## Original inverse finish against the literal result (internal progress)

`jet_secp_modinv_var_result.exec_inv_finish_literal` connects the original
finishing execution, copy-back and five-local reclamation to
`literal_invert_numeric`, preserving canonical storage, ownership, globals
and framing. The proof derives that the highest active limb's sign matches
the represented f value. At a stopped nonzero trajectory, the existing
divstep gcd theorem and checked field-prime bridge give `abs(f)=1`; the
coefficient link then identifies the exact modular inverse. A normalization
adapter retains the literal result for the original 256-bit word before C's
canonical input normalization, including the word equal to the modulus.

Zero input is included under its own coefficient invariant, not discarded:
`inv_seed_coefficient_zero` establishes that invariant at the actual seed,
and `inv_trajectory_zero_coefficient` preserves it using the canonical zero-g
matrix and the exact numeric coefficient equation furnished by the checked
C-update theorem. The coefficient link alone is insufficient for zero.

`exec_inv_after_divsteps_invariant` also returns this case directly from
the actual post-batch C execution: if the incoming canonical g is zero,
the control flow returns `Out_break` and the d coefficient is unchanged
modulo the field prime. This adds a conclusion, with no new premise, and
retains every previous execution/state/bounds/framing conclusion. The two
shared zero-matrix/update lemmas live in `jet_secp_modinv_var_invariant` so
both the C execution theorem and the literal-result bridge reuse them.

This is a terminal-state suffix theorem, not a whole inverse call. Its
terminal trajectory, stopped g, coefficient link, bounds and zero invariant
must still be connected by the complete actual loop; the CTZ boundary and
public jet composition remain open. The zero-preservation lemma takes the
numeric update fact already returned by the execution proof; it does not
assume an unproved execution or add an external model. No public theorem is
registered; coverage remains 514/533.

```sh
JET_TARGETS="C/jet_secp_modinv_var_result.vo C/jet_secp_modinv_var_first_batch.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_result C.jet_secp_modinv_var_first_batch
```

## Preserve inverse loop ranges through actual updates and shrinking

`exec_inv_after_divsteps_invariant` now additionally proves that an incoming
`inv_fg_value_capacity len rho` is preserved at the actual next length,
together with `inv_fg_limb_bounds` for **all five stored words**, including
inactive slots. No premise is added, and all previous conclusions remain;
this is an additional conditional preservation result.
`inv_entry_establishes_invariant` also returns both initial bounds, derived
from the represented input and actual initialization. Initial canonical low
digits are not required for the sparse modulus's negative first limb.

`jet_secp_signed62_ranges` supplies the radix value window and sharp top-limb
bound. `jet_secp_modinv_var_ranges` combines the existing helper loop bounds
for non-top stored slots with that top bound, then uses the real shortening
guard and sign-extension formula. A discarded top of 0 or -1 establishes
the smaller capacity while staying bounded as an inactive stored word.
The inclusive bound `abs(limb)<=2^62` retains the legitimate -2^62 case.
Canonical divstep contraction is reused from `fgBounds`, not postulated.

This closes the machine-bound recurrence needed for the next batch; it does
not execute the deferred CTZ call or the complete batch/outer loop, nor add
public coverage. Coverage remains 514/533. Rebuild and kernel-check the result
and first-batch modules with the command above; their dependency closures
include both range modules.

## General inverse batch entry (internal progress)

`jet_secp_modinv_var_batch_entry.inv_batch_setup` generalizes the actual
low-word loads, argument evaluation, callee entry and initializer execution
to every represented canonical batch state and valid active length, including
one-limb and negative signed-limb states. The low-62-bit correspondence to
the active f/g integer values is derived using `s62_value_mod_low` and the
unsigned/signed word congruence, without assuming nonnegative digits.

The first-batch execution/argument proofs now reuse value-parameterized
helpers in `jet_secp_modinv_var_first_batch`; their original contracts are
retained. `inv_pre_batch_forget` transfers a completed caller representation
to the common pre-batch layout by forgetting only obsolete matrix values,
retaining the actual buffer's Freeable ownership. It never initializes
memory or changes C code. The original statement-source equality is retained.

This completes entry setup, not the full divstep call or loop. CTZ behavior,
complete batch execution/return and outer-loop/public composition remain
unfinished. No new external model or public coverage is introduced; coverage
remains 514/533.

```sh
JET_TARGETS="C/jet_secp_modinv_var_batch_entry.vo C/jet_secp_modinv_var_result.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_batch_entry C.jet_secp_modinv_var_result
```

## Inverse batch final-store adapter (internal progress)

`jet_secp_modinv_var_batch_exit.exec_inv_batch_exit` executes the original
four matrix stores and eta return from the terminal divstep invariant. It
derives the exact stored machine words, restores `inv_loop_regs` from the
pre-batch layout with an undefined but owned matrix, and establishes
`inv_matrix_matches` for the canonical 62-step transformation. All other
caller regions are preserved using their existing separation and the actual
store frame; no matrix initialization or output-load premise is added to
this execution theorem. Only the four matrix slots change in the value map.

This connects the terminal store boundary to the representation required by
the existing post-batch update proof. It does not show that the complete
batch reaches that boundary: actual CTZ behavior, full batch/outer-loop
execution and public jet composition remain open. No new external model or
public coverage is introduced; coverage remains 514/533.

```sh
JET_TARGETS=C/jet_secp_modinv_var_batch_exit.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_batch_exit
```

## Stored inverse matrix through caller updates (internal progress)

`jet_secp_modinv_var_batch_update.exec_inv_after_stored_batch` starts with
the representation returned by `exec_inv_batch_exit` and the caller's
returned eta temporary. It executes the original eta assignment followed by
the coefficient/f-g updates and stop/shrink control. The pre-store coefficient
link, canonical state match and machine bounds are transported to the stored
matrix map; matrix matching and row bounds are derived, not assumed.

The result retains the update proof's exact numeric equations, next state,
length, coefficient link, bounds/capacity preservation, zero-input coefficient
preservation, stop condition and memory frame. It additionally proves the
next eta temporary and frames every other unmodified caller temporary. This
closes the caller-side invariant connection from the batch's stored matrix
to the next batch. It does not execute the missing divstep loop or establish
the return temporary from a complete call: those remain required before
whole-inverse/public composition. CTZ is still deferred and coverage is
unchanged at 514/533.

```sh
JET_TARGETS=C/jet_secp_modinv_var_batch_update.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_var_batch_update
```

## Complete divstep batch factored at CTZ (internal conditional progress)

`jet_secp_div62_loop.eval_div62_from_count_calls` composes the original
function entry, seven initializers, enclosing loop, four matrix stores and
return/free boundary. Every continuation strictly increases the canonical
trajectory index, so the loop terminates within its finite 62-step progress
budget. The result gives the exact stored matrix words, their signed canonical
values, the returned canonical eta, retained matrix ownership and the outside
memory frame. Initial matrix contents are not assumed.

**Explicit remaining premise:** at this memory, each nonzero-word call of the
original `secp256k1_ctz64_var` must execute silently, return the mathematical
trailing-zero count and leave memory unchanged. This is a generalized premise
of an internal composition lemma, not a new external-call model or an axiom,
and is not proved here. The nonzero argument is derived for every actual
sentinel call. Counting behavior is not inferred from the generic external
properties. This result is not a public jet equivalence or divergence and
does not change coverage (514/533).

The next consumer is the scalar-specific complete inverse batch: restore
the caller representation from these stores, execute eta assignment and the
existing scalar update/control theorem. Full outer-loop composition,
termination, and public reader/inverse/writer composition remain required,
as does eventual discharge of CTZ. No frozen target is changed.

```sh
JET_TARGETS=C/jet_secp_div62_loop.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_div62_loop
```

## Complete scalar inverse batch (internal conditional progress)

`jet_secp_scalar_inverse_batch.exec_scalar_inv_batch` executes one complete
original inverse loop body, including the caller's loads, the entire divstep
function, eta assignment, the scalar-modulus coefficient update, the `f/g`
update, and stop/shortening control. The incoming matrix may be undefined;
its canonical correspondence is derived from the divstep execution rather
than assumed. `jet_secp_modinv_batch_modulus` provides shared caller loading
and representation restoration for arbitrary six-word modulus metadata,
including the real scalar metadata (not the field modulus).

The scalar batch establishes the next canonical state, coefficient link,
limb and active-value bounds, eta and length, zero-input coefficient
preservation, and the break condition exactly when the next canonical `g`
is zero. It also frames unmodified temporaries and memory outside the batch's
matrix/update footprints. The checked forget adapter converts a completed
batch's state to the next batch's input representation without losing
ownership; no matrix-value initialization is needed.

The CTZ execution premise from the preceding section remains explicit at
the batch's input memory. This is internal conditional composition, not a
discharged library premise or accepted public jet. Whole-outer-loop
termination and finish/unpack/public-frame composition remain required.
Neither frozen targets nor the public coverage ledger are changed (514/533).

```sh
JET_TARGETS="C/jet_secp_modinv_batch_modulus.vo C/jet_secp_scalar_inverse_batch.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinv_batch_modulus C.jet_secp_scalar_inverse_batch
```

## Complete scalar inverse outer loop (internal conditional progress)

`jet_secp_scalar_inverse_loop.exec_scalar_inv_loop` executes the original
outer `modinv64_var` loop through its actual break, preserving the represented
scalar state, coefficient relation, canonical trajectory, eta/length,
limb/value bounds and the zero-input coefficient invariant. Its stopping
state has canonical `g=0` and the low-limb bounds needed by the existing
sign/normalization finishing proof. The batch theorem is strengthened only
by retaining those already derived low-limb bounds in its conclusion.

Termination is derived from the existing integer divstep termination theorem,
not assumed as a fixed iteration bound. The fuel proof consumes 62 canonical
steps per continuing batch. Even zero input executes a real batch before
breaking, matching C rather than exiting artificially at loop entry. Eta
safety follows from the existing live-trajectory bounds. The initial ready
invariant is derived from the actual initialized/copy-complete seed by
`scalar_inv_seed_ready`; matrix initialization is still unnecessary.

The internal execution premise is now quantified over memories, since each
outer batch updates its storage before the next CTZ call. The original CTZ
helper must execute silently, count correctly on nonzero words, and preserve
memory. This remains an unresolved premise, not a new external model or an
accepted public result. Core finish/free composition, outer unpack and public
frame composition, and eventual CTZ discharge remain required. Frozen targets
and public coverage remain unchanged (514/533).

```sh
JET_TARGETS="C/jet_secp_scalar_inverse_batch.vo C/jet_secp_scalar_inverse_loop.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_inverse_batch C.jet_secp_scalar_inverse_loop
```

## Scalar loop through literal result and cleanup (internal conditional progress)

`jet_secp_scalar_inverse_loop_finish.exec_scalar_inv_loop_finish` composes
the actual original loop, terminal sign load, scalar-order normalization,
copy-back and all five frees. The loop-exit representation discharges the
finishing theorem's storage, ownership, modulus contents, limb bounds,
coefficient link, terminal trajectory and zero-input coefficient premises;
none is assumed as a finished execution or result.

The returned words are normalized and equal the literal scalar-inversion
numeric result. The theorem also retains the explicit bridge to the literal
Simplicity word program for an input whose value reduces to the represented
scalar. It preserves input-object ownership, the scalar modulus global, and
the composed loop/finish memory frame. Shared array extraction and actual
six-word modulus reconstruction are proved from the current representation.

This starts at the ready-to-loop boundary, not at the public jet entry.
Composition with the actual core entry/initialization, enclosing scalar
unpack and public frame lifecycle still remains. The original CTZ helper's
execution remains a generalized internal premise over memories and nonzero
words; it is not discharged by this composition. There is no new external
model or public coverage entry, and frozen targets remain unchanged.

```sh
JET_TARGETS=C/jet_secp_scalar_inverse_loop_finish.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_inverse_loop_finish
```

## Complete scalar inverse helper calls (internal conditional progress)

`jet_secp_scalar_inverse_core.eval_scalar_inv_core` executes the entire
original `modinv64_var` function with the actual scalar modulus: function
entry and five local allocations, fourteen initializer/copy statements,
the complete loop, normalization, copy-back, and all local frees. Its input
is normalized signed62 storage with canonical scalar value, actual modulus
contents and ownership, not an assumed initialized loop or terminal result.
The returned words have the literal Simplicity scalar-inversion value.

`jet_secp_scalar_inverse_var.eval_scalar_inverse_var` then executes the
entire original `scalar_inverse_var`: its actual private allocation, packing,
complete core call, unpacking and cleanup. The result is a stored 32-byte
scalar whose integer value equals the literal scalar-inversion result, with
an explicit word-program bridge. Input/output scalar aliasing is allowed.
The input canonical-value condition is internal to this scalar helper;
the public jet's existing reader must establish it by reducing its input.

**Framing limit:** the core frame excludes the input object and the modulus
global block; the enclosing scalar frame excludes its input/output scalar
objects and that global block. The actual six modulus words and readability
are preserved separately. This is not a proof that every byte/permission of
the entire global block is framed, and must not be presented as such.
Fresh-local exclusion is discharged from real allocation, not imposed on
old caller blocks. Whole-public reader/writer and frame composition remain.

Both internal theorems retain the explicit deferred CTZ execution premise
over memories and nonzero words. No external model, frozen target, public
theorem contract or coverage row changes. Coverage remains 514/533.

```sh
JET_TARGETS="C/jet_secp_scalar_inverse_core.vo C/jet_secp_scalar_inverse_var.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_inverse_core C.jet_secp_scalar_inverse_var
```

## Scalar readiness from the actual initializer (proof support)

`jet_secp_modinfo_scalar_initialized` proves the actual scalar modulus's
exact permission bounds: its readable interval is `[0,48)`, with no writable
permission. Together with the six initialized words this defines
`modinfo_scalar_initialized`. The predicate is derived from `Genv.init_mem`
of the unchanged program; an initialized memory is proved to exist.
It implies the earlier `modinfo_scalar_state` without replacing that predicate.
Its old-block transport lemma matches the guarantees of fresh-frame
construction and adds no input/global disjointness requirement.

The intended public target is the **existing**
`secp_jet_initialized_local_spec`, which retains output, prefix, cursor and
arbitrary-chunk framing and additionally preserves readiness. It is distinct
from the unrestricted arbitrary-memory template; neither template is edited.
The complete scalar helper above still requires CTZ and still excludes the
modulus block from its byte frame. Closing that exclusion requires actual
readonly preservation of the constructed execution, not just its six word
loads. Reuse the existing allocation/store/free preservation results and
memory-identical count-call witnesses; do not silently import determinism or
generic external-call properties as an unchanged six-assumption proof.
Public read/write composition, readiness preservation through its real caller,
and CTZ discharge remain open. This adds no public coverage.

```sh
JET_TARGETS=C/jet_secp_modinfo_scalar_initialized.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_modinfo_scalar_initialized
```

## Complete scalar-helper modulus byte frame (internal conditional progress)

`jet_secp_scalar_inverse_initialized.eval_scalar_inverse_var_initialized`
closes the modulus-block exclusion described above. It returns the complete
original scalar inverse call, its literal output bridge, preserved initialized
state, and a memory frame excluding only the caller's scalar input/output
objects. The modulus block is no longer excluded: arbitrary chunks and
permissions there are covered by the existing `readonly_region_lframe` proof.
Scalar input/output aliasing remains allowed.

The proof now carries `readonly_preserved` through the **same constructed
execution**: divstep final stores, coefficient/f-g updates, outer batches,
finish, allocation/copy preparation, unpacking and frees. Count-call witnesses
return the identical memory, so no preservation fact about some other CTZ
execution, determinism argument, or generic external-call-properties axiom
is used. Earlier execution/numeric/framing conclusions are retained; the
changed internal contracts only append preservation certificates.

`jet_secp_closed_helpers` reuses the existing internal-Clight preservation
mechanism. It checks a 94-function subset of the unchanged helper table for
actual linkage, closed calls and non-function locals. The table is a proof
subset, not a replacement implementation; CTZ and open call paths are excluded.
Only identifiers are materialized during subset selection, avoiding repeated
normalization of all generated function bodies in symbolic proof terms.

The original CTZ execution premise remains unresolved. Full public
read/invert/write execution and initialized caller preservation still need
composition, and coverage remains 514/533. No C, AST, canonical specification,
API, generation setting or external-call model is changed.

```sh
JET_TARGETS="C/jet_secp_closed_helpers.vo C/jet_secp_scalar_inverse_initialized.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_closed_helpers C.jet_secp_scalar_inverse_initialized
```

## Complete original scalar-invert public caller (conditional progress)

`jet_secp_scalar_invert_local.scalar_invert_initialized_local_spec_from_count_calls`
now proves the **existing full initialized local contract** for
`f_simplicity_scalar_invert` and `literal_scalar_invert`, conditional on the
previously explicit CTZ-helper executions. This supersedes the remaining public
composition obligations in the preceding scalar-inverse progress sections.
The arbitrary valid caller-frame contract is not replaced by the fresh-frame
example, nor is the older arbitrary-memory contract silently given startup
facts.

The original public function is composed end to end: its 16- and 32-byte local
allocations, by-value source-frame copy, scalar reader, in-place inverse,
serializer, Boolean return, and local frees. Exact output cells, output prefix,
cursor movement, arbitrary-chunk caller framing, and initialized modulus state
are all conclusions. The reader's normalization is bridged to the literal
inverse of the original input, not substituted as a new specification.

`jet_secp_scalar_io_preserve` extends the checked internal-call subset to the
original reader/writer and their frame helpers (114 functions), reusing the
existing internal-Clight preservation proof. `Mem.unchanged_on` directly gives
complete readonly-block load and permission preservation. Hence the modulus
survives the same constructed read/invert/write execution, even if the input
frame refers to it; no blanket input/global separation, final-readability
premise, determinism, or generic external-call-properties axiom is added.

`jet_secp_scalar_invert_fresh.scalar_invert_runs_from_actual_init` separately
constructs frames for every Word256 input from actual
`Genv.init_mem jets_secp.prog`, establishes readiness, executes that whole public
function, and preserves all old program-memory loads. Its only deferred
execution premise is the same CTZ call obligation; frame/global premises are
discharged rather than assumed.

**This is still conditional progress, not accepted coverage.** The CTZ premise
is not an axiom, a newly installed external model, or a proved property of the
original builtin. It remains an explicit theorem parameter. The public ledger
stays at 514/533; no production C, generated AST, canonical specification,
primitive identity, API, or generation setting is changed.

```sh
JET_TARGETS="C/jet_secp_scalar_invert_local.vo C/jet_secp_scalar_invert_fresh.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_invert_local C.jet_secp_scalar_invert_fresh
```

## Complete original field-modulus inverse core (conditional progress)

`jet_secp_fe_inverse_core.eval_field_inv_core` now executes the complete
original `secp256k1_modinv64_var` with the **field** modulus global. Given
normalized signed62 input below `feP`, its actual stored output has the exact
literal inverse value. The Word256 bridge retains the literal result for the
original input, including normalization modulo `feP`.

The proof reuses the existing field coefficient/f-g/control invariant and
finishing proof, together with the modulus-independent divstep batch. New
composition modules establish each complete loop body, the terminating outer
loop, the zero-input coefficient invariant, initialization from the actual
caller prefix, sign normalization, copy-back and all five local frees.
Termination uses the existing divstep termination theorem, not an assumed
iteration count. Bounds on inactive limbs, shrinking active length and eta
are retained throughout. `readonly_preserved` is carried through the same
constructed execution.

The core's frame excludes its input object and modulus block; represented
modulus words/readability and the readonly-preservation certificate are
separate conclusions. This is **not** yet the surrounding `fe_inv_var`
copy/normalize/pack/unpack caller or the public `simplicity_fe_invert` jet.
Those callers can reuse the existing `jet_secp_fe_inv_prefix` and
`jet_secp_fe_inv_finish` proofs; no second field arithmetic framework or
alternative C implementation has been introduced.

As for scalar inversion, the original CTZ call behavior is still an explicit
theorem parameter, not a discharged dependency or a new external model.
Coverage remains 514/533. No production C, generated AST, specification,
primitive identity, API or generation setting is changed.

```sh
JET_TARGETS="C/jet_secp_fe_inverse_batch.vo C/jet_secp_fe_inverse_loop.vo C/jet_secp_fe_inverse_loop_finish.vo C/jet_secp_fe_inverse_core.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_fe_inverse_batch C.jet_secp_fe_inverse_loop C.jet_secp_fe_inverse_loop_finish C.jet_secp_fe_inverse_core
```

## Complete original `fe_inv_var` caller (conditional progress)

`jet_secp_fe_inverse_var.eval_fe_inverse_var_slice` now composes the original
field inverse helper end to end: actual two-local allocation, source-field
copy, normalization, signed62 packing, field-modulus inverse core, unpacking
to the requested output slice, and both local frees. It reuses
`jet_secp_fe_inv_prefix` and `jet_secp_fe_inv_finish`; the preceding core call
is derived from its input storage, not assumed as an output/execution premise.

The result includes actual execution, output storage and limb bounds, literal
inverse value/Word256 bridge, complete output-allocation ownership, preserved
field-modulus startup state, and arbitrary-chunk framing outside the output
slice. Input and output may coincide. The modulus global is **not** excluded
from that frame: `jet_secp_fe_inverse_state` uses the existing
`modinfo_fe_state`, actual readonly-preservation certificate and shared
`preserved_readonly_block_frame` lemma. No final-global-readability or blanket
input/global separation premise is added. The original startup theorem
`modinfo_fe_state_initial` establishes this state from `Genv.init_mem`.

`eval_fe_inverse_var` specializes this to whole 40-byte fields.
`eval_fe_inverse_var_point` executes the real point-normalization call that
inverts Z in place at byte offset 80, preserving X/Y, bytes outside Z, and
ownership of the complete 128-byte point allocation.

The original CTZ behavior remains the explicit deferred parameter. These are
complete **conditional helper** results, not yet the public
`simplicity_fe_invert` read/invert/write/return jet. Public caller composition
and CTZ discharge remain open; accepted coverage stays at 514/533. Production
C, generated ASTs, canonical specifications, primitive identities, API and
generation settings are unchanged.

```sh
JET_TARGETS="C/jet_secp_fe_inverse_state.vo C/jet_secp_fe_inverse_var.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_fe_inverse_state C.jet_secp_fe_inverse_var
```

## Complete original public `fe_invert` caller (conditional progress)

`jet_secp_fe_invert_local.fe_invert_initialized_local_spec_from_count_calls`
establishes the existing full initialized local contract for the original
`simplicity_fe_invert` jet and its literal Simplicity specification. The proof
composes actual function entry, source-frame copy, canonical field reader,
in-place inverse, original field writer, true return and both local frees.
The output word is derived from the inverse's stored limbs, not assumed as a
writer or arithmetic premise. Input normalization preserves the literal
specification for every Word256 input, including zero and noncanonical fields.

The result retains arbitrary valid caller cursors and frames, output prefix,
arbitrary-chunk memory framing, and the existing `modinfo_fe_state` startup
state. Shared reader/writer preservation results carry readonly memory through
the same constructed executions. The modulus block is not excluded from the
public memory frame, and no final-global-readability premise is required.

`jet_secp_fe_invert_fresh.field_invert_runs_from_actual_init` additionally
constructs valid frames for every input from the original program's actual
`Genv.init_mem`. The field-modulus state is established there and preserved
through fresh frame allocation and the full jet execution; all pre-existing
program-memory loads are retained.

The original CTZ call's execution and result remain the explicit deferred
parameter of these theorems. This is a complete **conditional public caller**
composition, not a discharged CTZ dependency or an accepted coverage row.
Accepted coverage remains 514/533. No new external-call model, production C,
generated AST, specification, primitive identity, API or generation setting is
introduced or changed. Snapshot audits distinguish this parameter from the
inherited axioms; recursive kernel checking does not discharge it.

With the pinned dependencies from `Coq/JET_BUILD.md`:

```sh
JET_TARGETS="C/jet_secp_fe_invert_local.vo C/jet_secp_fe_invert_fresh.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_fe_invert_local C.jet_secp_fe_invert_fresh
```

## Complete finite affine conversion and literal payload (conditional progress)

`jet_secp_affine_inverse_complete.eval_affine_finite_initialized` composes the
original finite `secp256k1_ge_set_gej_var` call, including both actual local
allocations, finite-flag test, in-place Z inverse at byte offset 80, all four
arithmetic calls, point/result stores and both local frees. It reuses the
checked field inverse caller and existing post-inverse arithmetic; neither
inverse execution nor its output is an extra premise. The field-modulus
startup state, readonly memory and arbitrary-chunk framing outside the two
caller-owned point objects survive the same constructed execution.

`jet_secp_affine_inverse_literal.eval_affine_finite_write_literal` starts with
the canonical XYZ storage produced by the existing reader and an already
written finite tag. It runs that complete helper and the original `write_ge`,
deriving the exact literal `gej_norm` payload for every input with those
represented fields. The literal inverse is proved invariant under the reader's
field normalization, so noncanonical original words are not excluded. Point
ownership, the output prefix/frame and field-modulus state are preserved.

This closes the previous inverse boundary in the finite normalization payload.
It does **not** yet compose the public `simplicity_gej_normalize` entry,
read/tag, both branches, return and public local frees. The finite-flag and
already-written-tag premises here are internal composition interfaces, not
new public input restrictions. CTZ behavior remains explicit and deferred;
accepted coverage remains 514/533. All frozen targets are unchanged.

```sh
JET_TARGETS="C/jet_secp_affine_inverse_complete.vo C/jet_secp_affine_inverse_literal.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_affine_inverse_complete C.jet_secp_affine_inverse_literal
```

## Complete original public `gej_normalize` caller (conditional progress)

`jet_secp_gej_norm_local.gej_normalize_initialized_local_spec_from_count_calls`
establishes the existing full initialized local contract for the original
public `simplicity_gej_normalize` and its literal Simplicity specification.
`jet_secp_gej_norm_lifecycle.eval_gej_normalize_initialized` composes actual
function entry, by-value source-frame copy, XYZ reader and tag writer, both
branches, true return and all three public local frees. The finite branch
executes the complete original affine/inverse caller and field writer; the
infinity branch executes the original `skip_ge`, including both `skip_fe`
calls. No curve membership, nonzero coordinate, canonical-word or branch
restriction is imposed on public inputs.

The result retains arbitrary valid caller cursors and frames, output prefix,
arbitrary-chunk memory framing, and the existing field-modulus startup state.
`jet_secp_gej_norm_fresh.gej_normalize_runs_from_actual_init` constructs fresh
frames for every input from the original program's actual `Genv.init_mem`,
establishes startup state there, and preserves all pre-existing program-memory
loads through the call. No input/global disjointness or final-readability
premise is introduced.

`jet_secp_frame_preserve` proves readonly preservation through the original
bit-write and skip helpers. Their assertion prefixes are syntactically present
in the frozen AST but guarded by the constant false expression `!1`. The proof
uses actual Clight evaluation to show that the original prefix changes no
memory, then applies the existing checked internal-helper preservation theorem
to the original suffix. It does not erase or replace AST nodes, alter a build
setting, assume assertion behavior, or rely on external-call-properties
axioms. Reader/tag, finite arithmetic and frees preserve readonly memory along
the same executions used by the public theorem.

The original CTZ execution/result remains the explicit deferred theorem
parameter. Thus this is a complete **conditional public caller**, not a
discharged external dependency or accepted coverage row. Coverage remains
514/533. Production C, original specifications and identities, API contracts,
generated ASTs and generation settings are unchanged.

```sh
JET_TARGETS="C/jet_secp_gej_norm_local.vo C/jet_secp_gej_norm_fresh.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_norm_local C.jet_secp_gej_norm_fresh
```

## Complete original public `gej_y_is_odd` caller (conditional progress)

`jet_secp_gej_odd_local.gej_y_is_odd_initialized_local_spec_from_count_calls`
establishes the existing full initialized local contract for original
`simplicity_gej_y_is_odd`. The literal term preserves the composition in
`LibSecp256k1.hs:565`, including inversion, cube, multiplication and canonical
field parity. Its infinity result is proved false from the literal term, not
replaced by a special-case specification.

`jet_secp_gej_odd_lifecycle.eval_gej_y_is_odd_initialized` composes actual entry,
source-frame copy, XYZ reader, infinity accessor, both branches, true return
and all three public local frees. The finite branch executes the checked
original affine conversion, original Y normalizer, original parity accessor
and bit writer, deriving the exact literal bit. The infinity branch executes
the original false-bit write. No curve membership, nonzero coordinate,
canonical-word or branch restriction is added to public inputs.

The setup reuses the existing three-allocation normalization proof through
checked entry/copy adapters for the differently named affine local (`b`
instead of `r`). It does not substitute a function or allocation layout.
The result retains arbitrary valid frame/cursor layouts, output prefix,
arbitrary-chunk framing and the existing field-modulus startup state.
`jet_secp_gej_odd_fresh.gej_y_is_odd_runs_from_actual_init` establishes that
state at the original program's actual `Genv.init_mem`, constructs frames for
every input, and preserves all pre-existing program-memory loads.

Readonly preservation follows the same constructed executions, reusing the
original frame-helper preservation proofs. No new external-call model or
external-call-properties dependency is introduced. The original CTZ behavior
remains the explicit deferred theorem parameter, so this is a complete
**conditional public caller**, not an accepted coverage row. Coverage remains
514/533. All production/specification/AST/API/generation targets are unchanged.

```sh
JET_TARGETS="C/jet_secp_gej_odd_local.vo C/jet_secp_gej_odd_fresh.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_odd_local C.jet_secp_gej_odd_fresh
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
runtime failure, consensus discrepancy or exploit. An unconditional result
needs justified concrete external semantics/linkage. On 2026-10-27 the user
approved explicit `ctz_model` and `memset_model` premises as **conditional**
results, counted like `memcpy_model` (see the next section). Switching the production AST to a
fallback, changing compiler/generation configuration, or changing the target
would require separate explicit approval and is not done here.

## Approved explicit CTZ model: five conditional public jets

Policy change approved by the user on 2026-10-27: an explicit premise about
the abstract `__builtin_ctzl` external call is accepted as a conditional
result, reported like `memcpy_model`. No production C, AST, generation
setting, specification or API is changed, and nothing is asserted as an axiom.

`jet_ctz_model.ctz_model` states the GCC/Clang contract on 64-bit
`unsigned long`, restricted to nonzero arguments: for every global
environment, memory `m` and nonzero `x`,
`external_functions_sem "__builtin_ctzl" ([Tlong] -> Tint)` relates
`[Vlong x]`, `m` to `E0`, `Vint (Z_ctz x)`, `m`. `Z_ctz_pos_spec` and
`Z_ctz_bound` check that `Z_ctz` is the trailing-zero count, below 64.
`jet_ctz_model_consistent.ctz_model_consistent` is a closed
relative-consistency theorem: some assignment of semantics to every external
function satisfies CompCert's `extcall_properties` and this model. It does not
identify CompCert's parameter with that assignment.

`jet_secp_ctz_jets.ctz_model_count_calls` derives the previously deferred
premise, the complete original `secp256k1_ctz64_var` execution, from the model
and `eval_ctz64_from_external`. The following public theorems are each the
existing full initialized local contract with that one premise:

- `C.jet_secp_ctz_jets.fe_invert_initialized_local_spec`
- `C.jet_secp_ctz_jets.scalar_invert_initialized_local_spec`
- `C.jet_secp_ctz_jets.gej_normalize_initialized_local_spec`
- `C.jet_secp_ctz_jets.gej_y_is_odd_initialized_local_spec`
- `C.jet_secp_ctz_jets.swu_initialized_local_spec`

Their startup states (`modinfo_fe_state`, `modinfo_scalar_initialized`,
`swu_startup`) are established at the actual `Genv.init_mem` by the existing
`*_runs_from_actual_init`, `modinfo_scalar_initial_state_exists` and
`swu_startup_exists` theorems. All five retain only the six inherited
assumptions besides the visible `ctz_model` premise. `jet-coverage.py`
counts them as conditional (`ctz_model`), separately from direct proofs.

```sh
JET_TARGETS="C/jet_secp_ctz_jets.vo C/jet_ctz_model_consistent.vo" bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_ctz_jets C.jet_ctz_model_consistent
```

`hash_to_curve` and the inversions inside `scale`, `generate`,
`linear_combination_1` and the signature checks still need their own public
compositions (and, for ecmult, `memset_model`); they are not covered here.

