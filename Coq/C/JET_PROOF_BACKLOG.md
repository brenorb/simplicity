# Remaining jet proof work

## Current completion criterion: equivalence or proved divergence

The user clarified that 533/533 means **proof coverage**, permitting checked
implementation-to-specification divergence as well as equivalence. Keep the
two classifications separate. A restricted theorem, suspected mismatch,
native observation, or generic external-semantics countermodel is not a
whole-public divergence proof. Production C, specifications and APIs remain
fixed; report a proved mismatch rather than correcting either target.

The inventory currently has 521 equivalence entries (138 with the existing
explicit `memcpy_model` premise, 5 with the approved `ctz_model` premise, 3
with the approved `memset_model` premise) and one checked whole-public
refutation, `C.jet_secp_mixed_ex_refutation.gej_ge_add_ex_not_literal_local_spec`:
522/533 proof entries, with 11 jets still lacking either result. The
`scale`, `off_curve_scale` and `gej_is_on_curve` endpoints passed joint scoped
acceptance on the exact inputs of `18d941d3`; accepted coverage is now
522/533. The earlier `off_curve_scale` acceptance at `5e87dacb` remains
historical evidence for those earlier inputs. The
user approved explicit `ctz_model`/`memset_model` premises as conditional
coverage on 2026-10-27; a SHA empty-preimage premise for the fee jets was not
approved (see `JET_SECP_EXTERNAL_MISMATCHES.md`). Registration
is not fresh acceptance. The endpoint-generalization candidate passed full
ordinary acceptance at `6a227e8b` and is integrated in `58f36fe9`; later-added
modules are checked separately as described in `JET_ACCEPTANCE.md`.
Historical equivalence-only counts and the obstruction to
533 positive equivalences below are retained as such, not as an obstruction
to the newly clarified mixed-outcome proof goal.

`python3 Coq/jet-coverage.py --require-complete` now checks this proof-coverage
criterion, while printing equivalence, explicit libc conditions and divergence
separately. It requires the exact public refutation type, its audited theorem
and its mismatch report; its mutation tests reject conditional negations and
wrong implementation/specification targets. Kernel checking and reviewed
statement/assumption records remain required by `check-jets.sh`.

`jet_secp_checked_scale_local.checked_scale_initialized_local_spec` covers success and assertion
failure for all scalar/coordinate words, derives the original wrapper's
allocations, readers, validity test, multiplication, writer and frees, and
establishes/preserves startup for the distinct `_ng__1` global. Its only extra
library premise is `memset_model`. Shared multiplication helpers now
parameterize their readonly zero-scalar block, retaining the old interfaces
as exact specializations. The strengthened curve-check helpers prove
coordinate/flag readback and retain their previous interfaces as projections.
All three affected public endpoints passed joint acceptance: kernel checking
on 999 modules, matching assumption records on 929 modules and contract
records on 948 modules, negative tests, and five AST regeneration comparisons.
The source checker binds Scale's CoreJets
constructor, Haskell assertion tree, FFI entry, startup and literal ports;
21 targeted mutations reject source/contract drift. Reproduce with
`bash Coq/check-jets.sh --accept --jets=simplicity_off_curve_scale,simplicity_scale,simplicity_gej_is_on_curve`.
The next reserved jet is `off_curve_linear_combination_1`: compose the
arbitrary-global-Z generator bridge with the four-stream descending loop and
actual preprocessing/outer caller. No inverse, nonzero-Z or on-curve premise
may be imposed on this off-curve caller.

`jet_secp_zinv_general_{numeric,literal,outputs,call}` now supplies the
arbitrary-Z bridge in the ordinary build. `eval_zinv_scaled_literal` reuses
the original finite/infinite C executions and proves their exact output is
`literal_gej_ge_add (acc, literal_gej_zinv (affine, s))`. Zero scale and all
H/I branches are included. Bounds, stored flag, ownership and framing are
retained. The four-module build and reviewed statement/assumption comparisons
pass with no new axioms; recursive acceptance is pending composition into the
reserved public caller. This helper batch adds no jet to coverage.
`jet_secp_generator_{digit,dispatch,pair}_general` lifts that result through
the original lookup, guarded digit reads and both generator dispatches.
Absent digits retain exact decoded accumulator equality. The pair result
preserves the factor, generator tables, ownership and external framing;
closed-call effects prove permission/readonly preservation. These three
ordinary modules pass their build and reviewed record comparisons. Whole-jet
composition and recursive acceptance remain pending.
`jet_secp_strauss_point_prefix` and `jet_secp_strauss_general_{iteration,loop,
loop_literal,point_stage}` now compose the original double, ordinary/lambda
point digits and both generator digits in their exact order. The terminating
loop carries four streams, relates its shortened run to all 129 literal steps,
and the full point stage derives infinity initialization and final Z correction.
The final correction deliberately does not assert flag/Z agreement when the
shared Z is zero. These five ordinary modules compile and pass scoped record
comparisons with the inherited axiom set. Build both
`C/jet_secp_strauss_general_point_stage.vo` and
`C/jet_secp_strauss_general_loop_literal.vo` through `JET_TARGETS`; neither
root alone builds both branches of this batch. The preprocessing/main caller
and public contract still need composition; accepted coverage stays 522/533.
`jet_secp_generator_wnaf_general` keeps an arbitrary incoming point-bit count
when both generator wNAF lengths raise the loop bound. Reuse it instead of
the older generator-only setup, whose incoming count is zero.
`jet_secp_strauss_general_arrays.strauss_body_from_four_arrays` identifies all
four actual arrays with the literal full Strauss body.
`jet_secp_strauss_generator_branch.exec_strauss_generator_branch` derives the
original nonnull branch's scalar split, wNAF calls and maximum updates from
the approved `memset_model`; it does not leave desired clear executions as
premises. These three ordinary modules pass both explicit build roots
(`C/jet_secp_strauss_general_arrays.vo` and
`C/jet_secp_strauss_generator_branch.vo`) and scoped record comparisons.
The next step is the finite/nonzero-point main caller, followed by the skipped
point branch, whole Strauss/ecmult calls and public wrapper. These internal
results add no accepted jet and await recursive checking with that endpoint.
`jet_secp_strauss_general_main.exec_strauss_general_main` now composes that
nonnull generator preprocessing with the point stage for a prepared ordinary
point table. It covers an arbitrary generator scalar, preserves the previous
point bit count, proves the exact full literal Strauss body, and retains
ownership, generator tables and external framing. The ordinary root build
and scoped statement/assumption comparison pass; the sole extra library
premise is the existing `memset_model`.
Next, extend the actual whole Strauss caller using the existing finite-point
entry/preparation/free proof. Add the generator scalar as an owned outer
object and prove it survives preprocessing (including the readonly-global
exceptions); reuse this new main result. In the skipped-point case, reuse the
existing generator main stage at `no=0`, whose denominator is initialized to
one. Then compose ecmult and the public wrapper before registering a new jet.

The following paragraphs retain the earlier acceptance history, before the
later conditional CTZ/memset registrations above. Their 513/533 and
19-remaining counts are historical; the current proof inventory is 522/533
with 11 remaining.

That earlier local-contract registry counted 513 of the 533 header declarations
toward full-input contracts (138 still conditional on `memcpy_model`). A
separate restricted `gej_ge_add_ex` entry describes a reported mismatch and
does not count toward all-input completion.
Selected registrations, verification status and their conditions are listed in
[JET_ACCEPTANCE.md](JET_ACCEPTANCE.md); 20 declarations lack unrestricted
equivalence, of which one has the checked divergence above and 19 lack either
outcome.
The projective curve, doubling, mixed-addition, square-root, mixed-equivalence
and decompression endpoints passed ordinary scoped acceptance; that accepted
local-contract coverage was 513/533. The every-jet
goal remains incomplete, including shared obligations for conditional entries.
Projective addition passed scoped acceptance on `ba6b19e8`; the exact scope
and reproduction command are recorded in `JET_ACCEPTANCE.md`.
Projective equivalence passed ordinary scoped acceptance on `0cb928b9`;
it is included in the accepted count.

The remaining work includes:

- shared frame-domain and evaluator admissibility;
- exhaustive inherited correspondence to canonical programs;
- general caller startup and persistent SHA/global-state readiness;
- libc implementation proofs where a contract assumes `memcpy_model`;
- raw transaction/taproot projections for cached Bitcoin environment fields.

## Current inversion results (conditional on the CTZ model)

The original field/scalar inverse batches, terminating outer loops and complete
inverse helper callers are now composed. Full initialized public contracts
and actual-program-initialization execution witnesses are checked for
`fe_invert`, `scalar_invert`, `gej_normalize` and `gej_y_is_odd`. Together with
`swu`, these are registered through `jet_secp_ctz_jets`, which derives the
original CTZ helper execution from the explicit `ctz_model` premise. They are
conditional coverage entries, not proofs of the actual builtin implementation.
Reuse these callers and the shared field/scalar
lemmas rather than rebuilding the conversion, loop or return proofs.
Current statements, remaining boundaries and reproducible commands are in
[JET_SECP_EXTERNAL_MISMATCHES.md](JET_SECP_EXTERNAL_MISMATCHES.md).

Russell O'Connor's hand-written modular-inverse proof is already in the
repository (introduced by `c1dddedd`, 2023-11-28). Reuse `C/modinv.v`:
`modInv_mul_unique_l` is already used by `jet_secp_invert_modinv` and
`jet_secp_scalar_invert_literal` to identify the literal Simplicity programs'
results with the same modular inverse, including separate zero/modulus cases.
The older C proof is
`secp256k1/verif_modinv64_impl.v:body_secp256k1_modinv64_var`. It is a VST
proof over `jets_secp256k1.v`, whose CTZ wrapper calls its internal de Bruijn
implementation. The current frozen `jets_secp.v` wrapper instead selects
`__builtin_ctzl`; `jet_secp_ctz_external_call` exhibits that exact boundary.
The old theorem is useful proof structure and arithmetic evidence, but does
not discharge that external call for the current program. Do not regenerate
the AST or replace the helper to import the old result. Concrete builtin
semantics/linkage remains outside these conditional contracts; their
modular-inverse mathematics and public caller compositions are already proved.

### Historical normalization-only milestone (superseded)

The following records the earlier normalizer milestone. Its then-missing
batch/loop implication has since been proved conditionally as described
above; the CTZ boundary remains open.

Reuse the completed signed62 conversion/storage and literal EEA bridges;
do not rebuild them. The original field `normalize_62` call is now proved
through `jet_secp_modinv_normalize62_{exec,global,words,numeric}`. The final
`eval_field_norm62_numeric` contract derives the actual call, canonical
signed62 output with value `(sign*input) mod p`, output ownership, retained
48-byte modulus metadata and byte-range framing. Its internal preconditions
match the C helper's stated limb/value bounds; the public inverse loop must
derive them, not assume them of arbitrary Word256 inputs. The numeric bridge
lemmas are closed; the call retains six inherited assumptions and no libc model.

The historical batch/loop implication and its normalization bounds are now
discharged by the complete conditional callers above. The actual builtin
implementation remains unverified; the model does not discharge itself. See
`JET_SECP_EXTERNAL_MISMATCHES.md` for precise results and reproduction commands.

## Completion constraints on the remaining thirteen jets and one proved divergence

A read-only Astra Medium strategy review, followed by inspection of the
existing refutation/report, confirms that changing the next jet alone does
not currently bypass the shared boundaries. The grouping below is a **source
call-graph inference**, not a new formal execution-extraction theorem for
each public caller. Early-failure/infinity subcases do not prove an all-input
contract.

| Remaining declarations (omit `simplicity_`) | Boundary |
| --- | --- |
| `hash_to_curve` | `ctz_model` handles the inverse helper dependency. Also prove that two accepted digest maps have a finite sum, or exhibit an actual common-key counterexample: `hash_public_return_agreement_iff` exposes this separate return/assertion boundary. Its reachability is unresolved. (`fe_invert`, `scalar_invert`, `gej_normalize`, `gej_y_is_odd`, `swu` are conditional on `ctz_model`.) |
| `off_curve_scale`, `scale`, `off_curve_linear_combination_1`, `linear_combination_1`, `linear_verify_1`, `point_verify_1` | General ecmult (point table, wNAF digits, Strauss loop); memset now has `memset_model`/`exec_wnaf_memset`. (`generate` is conditional on `memset_model`.) |
| `check_sig_verify`, `bip_0340_verify`, `bitcoin_build_taptweak`, `build_taptweak` | Their accepted branches reach multiplication/normalization and the external memset/ctz boundaries; x-only tweaking also directly calls memset. |
| `output_is_fee`, `total_fee` | Empty-script digest equality versus actual script emptiness; the converse remains unproved. The total-fee dependency is through cache construction. |
| `gej_ge_add_ex` | The existing whole-public literal contract is formally refuted, not merely missing a proof. |

The paths are in `C/jets-secp256k1.c`, `C/secp256k1/{ecmult,group,generator,
schnorrsig,extrakeys}_impl.h` and the inverse helpers. Exact source locations,
evidence and limits are in [JET_SECP_EXTERNAL_MISMATCHES.md](JET_SECP_EXTERNAL_MISMATCHES.md),
[JET_ELEMENTS_FEE_MISMATCHES.md](JET_ELEMENTS_FEE_MISMATCHES.md) and
[JET_SECP_RATIO_MISMATCHES.md](JET_SECP_RATIO_MISMATCHES.md).
`jet_secp_mixed_ex_refutation.gej_ge_add_ex_not_literal_local_spec` negates
the unrestricted fixed contract using the actual public counterexample and
Clight determinism. Thus **533/533 unrestricted equivalence cannot be reached
while that function, literal target and input domain all remain fixed**.
Keep the goal incomplete; do not count its restricted theorem or silently
change the completion criterion. A correction needs separate approval.

No existing ctz/memset linkage was found that discharges the frozen production
external parameter. The older ctz fallback is a different AST; a reference
memcpy proof or existence of a consistent external assignment does not prove
the actual fixed parameter has that behavior. The 138 existing conditional
rows also retain their explicitly reported libc obligation. Continue safe
proof/verification work, but do not hide these boundaries with another model
premise or substitute implementation.

## Bounded memcpy premise integrated

`1471be3d` integrates the reviewed `codex/bounded-memcpy-assumption` change:
the existing explicit library premise now guarantees copies of 1..64 bytes,
rather than every positive representable size. This assumes less library
behavior; the SHA helpers derive each new bound from their existing block
invariants. Public jet input, output and framing contracts are unchanged.
The library premise is still not discharged. The original review and source
inventories are in [JET_MEMCPY_BOUND_REVIEW.md](JET_MEMCPY_BOUND_REVIEW.md).

The current dependency inventory selects all 179 registered consumers of the
model (714 C modules), plus eight additional manifest roots. Including the
latter's dependencies gives 1,006 C modules, not merely 714 + 8. Validation of
these exact proof inputs passes: full affected build, independent recursive
kernel checking, matching assumption records across 818 modules and contract
records across 872 modules, gate-regression tests, all 104 global source/negative checks and all
five regenerated AST comparisons. There are no unsafe kernel features or
library axioms outside the existing allowlist, and verification inputs stayed
unchanged throughout the completed checks.

The first ordinary acceptance attempt passed its source checks, then stopped
on cached objects compiled with OCaml 4.14.1. The affected sources were rebuilt
under the existing Coq 8.17.1 / OCaml 4.14.4 toolchain; the remaining validation
phases then passed using the existing build, kernel, record and AST tools.
No proof source or target was changed to repair that cache mismatch. This is
combined phase validation of the complete affected scope, not a claim that
the interrupted command passed or that the entire repository was reaccepted.
The reproduction commands in the bounded-premise review derive the registered
scope from the current dependency graph and include the extra roots.

Coverage remains 513/533, including the same 138 conditional entries. Neither
this integration nor its larger checked dependency closure proves another jet
or resolves the reported ctz/memset, fee-hash or ratio boundaries.

## Fresh-frame witnesses for accepted secp contracts

`jet_secp_executable_registry` reuses the existing constructive frame theorem
for all 25 later frame-only secp registrations: field/scalar arithmetic,
point operations, predicates, equivalences and decompression. Together with
the three original instances in `jet_frame_constructible_secp`, this covers
all 28 currently registered frame-only secp jets. The two initialized-global
contracts and the restricted ratio contract are deliberately not treated as
frame-only results.

For every value of each original input type, arbitrary environment argument
and starting memory, the theorem constructs fresh input/output frames and a
complete call of the actual C jet, returning 1 and the encoded original
specification result, while preserving all pre-existing loads. No frame or
intermediate execution premise is left to the caller. These existential fresh
layouts do not replace the original general local contracts or prove whole
evaluator admissibility, and add no jet coverage.

Normal compilation and reviewed focused no-update statement/definition and
assumption checks pass. All 29 audited exports (the generic adapter, three
original instances and 25 new instances) retain exactly the same six inherited
assumptions, with no extra libc model. Independent recursive kernel checking
and the subsequent no-update records and frozen-target check pass on
`e39fb568` in the main checkout. Reproduce the build/check with:

```sh
JET_TARGETS=C/jet_secp_executable_registry.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_executable_registry
```

Rebuilding this closure exposed context-heavy separation searches and a large
closed symbolic-output comparison in existing dependencies. The proof-only
repairs use structural NoDup prefix facts, explicit disjunction cases, the
existing proved symbolic-expression recognizer, and explicit congruence types.
Their original statements, definitions, assumptions and timeouts are unchanged;
normal compilation and their existing no-update records pass. No target or
generation setting was changed.

`jet_secp_beta_fresh.beta_runs_from_actual_init` additionally discharges the
initialized beta global and frame premises for every Word256 input. It starts
with an existing memory from `Genv.init_mem jets_secp.prog`, constructs fresh
frames without changing any old load, derives readiness of the call memory,
and executes the original `simplicity_fe_multiply_beta`. The conclusion retains
the full `finv`, final readiness and preservation of old initialized-memory
loads. No readiness, layout or intermediate-execution premise remains in this
actual-init statement. The general initialized local contract is unchanged.

The two supporting memory lemmas use four inherited Coq assumptions; the two
execution theorems retain six, with no extra libc model. Full untruncated
types were reviewed using `Set Printing Depth 1000`; the existing snapshot
printer abbreviates these deeply nested conjunctions. Normal compilation and
reviewed no-update records pass. The existing lambda startup proof was rebuilt
without edits. Their joint independent recursive kernel check, subsequent
no-update records and frozen-target check pass on immutable `93b4d451` in the
secondary checkout. No unsafe, type-in-type or assumed-positivity flags are
reported. Reproduce with:

```sh
JET_TARGETS="C/jet_secp_beta_fresh.vo C/jet_secp_scalar_lambda_fresh.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_beta_fresh C.jet_secp_scalar_lambda_fresh
```

These are fresh-frame execution witnesses, not whole-evaluator startup or
acceptance of another jet. Coverage remains 513/533, including 138 existing
conditional entries; all previously reported mismatches remain unresolved.

## Bitcoin value/script hash frontier

`jet_bitcoin_value_hash_literal` now composes the checked original C getters
for `output_values_hash` and `input_values_hash` with the exact canonical
`hashWord64s (drop (primitive ...))` programs, including raw interpretation.
The four program/parametricity lemmas are closed; the four complete C call
contracts retain the six inherited assumptions and add no libc premise.
The original environment relation, frozen Bitcoin domain and represented
cache premises are unchanged. Cache construction is a separate obligation.
Normal compilation and reviewed focused snapshots pass; ordinary scoped
acceptance for these new registrations passed on the proof inputs of
`b42762b6`, bringing accepted coverage to 511/533. The existing source gate rejects 51 array-program
mutations and 26 raw-boundary mutations.

`jet_bitcoin_composite_hash_literal` similarly connects `outputs_hash` and
`input_utxos_hash` to their literal two-component SHA compositions, including
raw interpretation and the complete original getter calls. Its five pure
exports are closed; its four C contracts retain the same six inherited
assumptions, with no libc premise. The existing source gate fixes component
order, the SHA64 width, cache offsets and full boundaries, rejecting 22
mutations. Ordinary scoped acceptance for this pair passed in the same run.

`jet_bitcoin_indexed_hash_literal` ports the shared value/script-hash program
for `output_hash` and `input_utxo_hash`: exact primitive routing, absent-value
branch, script assertion, SHA8/SHA32 append and finalization. It composes the
original computing C calls, not a cache-returning replacement. The three pure
exports are closed; all four C contracts retain the six inherited assumptions
and the existing explicit `memcpy_model` premise. The source gate rejects 24
mutations, including removal or replacement of that premise. The raw/extended
environment relation and SHA-readiness conditions remain unchanged. Scoped
acceptance passed for all six new registrations; accepted local-contract
coverage is 511/533, including 138 conditional entries. This is not all-jet
completion or a discharge of the remaining shared obligations.

The ordinary six-jet acceptance run passed on `b42762b6`'s proof inputs
(identical audited inputs in the documentation-only descendant `191617fd`):
351 recursively kernel-checked modules, 222 assumption records, 245 contract
records, all source/negative checks and all five regenerated ASTs. The audit
input fingerprint was unchanged. Reproduce without update flags:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_values_hash,simplicity_bitcoin_input_values_hash,simplicity_bitcoin_outputs_hash,simplicity_bitcoin_input_utxos_hash,simplicity_bitcoin_output_hash,simplicity_bitcoin_input_utxo_hash
```

`jet_bitcoin_tx_sig_hash_literal` now connects the complete original `tx_hash`
and `sig_all_hash` calls to the exact literal transaction/signature compositions,
including raw interpretation. Its four pure exports are closed; the four C
contracts retain the six inherited assumptions and add no libc premise. The
normal module compiles under pinned Coq 8.17.1 / OCaml 4.14.4. The unchanged
original `jet_bitcoin_sig_all_hash` source was rebuilt under that baseline;
its existing assumption/contract records match without updates. Explicit
algebra arguments in the SHA rewrites avoid a generic-rewrite timeout. The
existing source gate rejects 22 mutations of routing, widths, cache offsets,
primitive semantics and complete boundaries.

The two registrations passed ordinary scoped acceptance on `f59d2305`:
294 recursively kernel-checked modules, 165 assumption records, 188 contract
records, all source/negative checks and all five regenerated ASTs, with unchanged
audit inputs. Accepted local-contract coverage is now 513/533 (375 without an
extra libc premise; 138 conditional on `memcpy_model`). They retain the frozen Bitcoin
domain and LockTime commitment-identity limits: value computations are proved,
not Coq/Haskell primitive identity equality. The dedicated task-owned
`jet-acceptance` worktree completed its clean six-jet dependency build and
passed the existing verifier on the fixed `f59d2305` commit (294-module
dependency closure). Keep future audited worktrees immutable until their runs
are terminal; development can continue independently in main. Reproduce with:

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_tx_hash,simplicity_bitcoin_sig_all_hash
```

This changes verification parallelism only, not generation settings or checked
inputs. Hardware was checked before increasing parallelism. The run's receipt
must remain scoped to that exact commit and input set.

## Active `generate` frontier

**Done (conditional):** `C.jet_secp_memset_jets.generate_initialized_local_spec`
discharges the memset-step premise below from `memset_model`; see
`JET_SECP_EXTERNAL_MISMATCHES.md`.

The existing `jet_secp_generate_local` already contains the complete public
`generate_initialized_local_spec_from_memset_steps` and
`generate_runs_from_actual_init`, retaining the explicit deferred original
memset-step premise. `jet_secp_generator_function`, `jet_secp_ecmult_generator`
and `jet_secp_generate_lifecycle` cover the original calls, entry, returns and
frees. Do not restart that lifecycle or the completed wNAF/point-loop proofs.
These are conditional results, not accepted whole-jet coverage. The earlier
milestones below record their construction; their then-pending composition
steps must not be mistaken for current missing proofs. Rebuild the actual
public root before making a fresh acceptance claim.

`jet_secp_wnaf5_literal` ports `wnaf5step1`, `wnafstepD` and `wnaf5`
(LibSecp256k1.hs 413--438, 609) with closed parametricity, digit-order and
length lemmas. Unlike window 15, `wnaf5step1` shifts before its parity
branch and emits the shifted word's low nibble (Coq `Word 2`) as the index
of the odd digit `2n+1`. Native evidence only (not a proof): on 15 scalars
including 0, 1, 2^127 and 2^128-1 its decoded digits equal a direct model of
C `secp256k1_ecmult_wnaf(w=5, len=129)` and sum back to the input.
`jet_secp_wnaf5_literal_next.literal_wnaf5_odd_next` (odd state: digit
`2n+1` equals C `wnaf_digit (q mod 32) 5`, next state `(q-digit)/2`) and
`jet_secp_wnaf5_literal_window` (even steps, zero runs, full five-bit window
`literal_wnaf_window5`) are closed, for sign bit 0.

**Sign handling (needed for the point path, not for generate).** The
literal state `(b, w)` denotes the signed 129-bit value `w - b*2^128`.
`scalar_split_lambda` halves can be negative; C then takes wNAF's negation
branch (`sign = -1` on the magnitude). Native evidence (14 magnitudes): the
literal digits of `(1, 2^128 - v)` equal C's negated `wnaf(v)` and sum to
`-v`. The window-15 chain only ever needed `b = 0`.
`jet_secp_wnaf_literal_signed` now integrates the general signed-subtraction
proof. `jet_secp_wnaf5_signed.literal_wnaf5_odd_signed` and
`literal_wnaf5_even_signed` prove the exact literal transitions for either
sign, deriving the next signed value `(q-digit)/2` and the odd digit
`wnaf_digit (q mod 32) 5`. The subtraction range is derived from the initial
state and nibble bounds, not added as a caller premise.
`literal_wnaf5_digit_negates` proves that odd negative residuals emit the
negation of the positive-magnitude C digit.
`jet_secp_wnaf5_signed_windows` lifts those transitions through arbitrary
signed zero runs and complete five-bit windows, retaining exact digit order
and the next signed residual. `jet_secp_wnaf5_signed_body` composes the
original C dispatch with its actual digit/store/state-update execution for
full windows and skips, including `sign = -1`. The full-window theorem retains
the stored literal digit, updated fields/carry, scalar storage and memory
effect; the skip theorem executes the actual `Out_continue` branch with
unchanged memory. Their initial signed-residual relation describes the
incoming state; no outgoing value or intermediate execution is assumed.
`jet_secp_wnaf5_signed_tail` covers the final partial window for either sign;
its quotient bound follows from the initial scalar/cursor bounds. It allows
magnitudes below `2^129`, including `2^128` when negatively represented.
`jet_secp_wnaf5_signed_nonzero` composes every actual nonzero C clamp (widths
1..5), and `jet_secp_wnaf5_signed_array` proves the complete body step while
preserving the array. C's magnitude digits retain their existing convention;
their stored signed values equal the literal segment's values.
`jet_secp_wnaf5_signed_loop.exec_wnaf5_loop_zero_signed` now executes all
original loop guards/branches, terminates, and returns the actual highest
nonzero index plus one. From initial zero buffer loads, it proves that all
129 stored signed digits equal the exact fixed `literal_wnaf5_digits` vector,
retaining the final carry, scalar storage, array, length bound, permissions
and memory frame. Its loop induction derives every intermediate body and
array relation rather than assuming a trace or final decoding relation.
`jet_secp_wnaf_function5.eval_wnaf_literal5` now composes the whole original
129/5 function: entry and allocation, actual `memset` under `memset_model`,
scalar copy, bit-255 test, either sign branch, every loop iteration, return
conversion and freeing the private scalar. Its signed input adapters in
`jet_secp_wnaf5_input` cover every `(Bit, Word128)` state, including `-2^128`,
and derive both the canonical scalar range and the sign/magnitude relation.
No intermediate execution, output equality or initialized digit buffer is
assumed at the whole-function boundary. The result retains the exact literal
digit vector, output ownership, input scalar, old permissions, outside-output
frame and readonly memory. It is helper progress, not new public coverage
(still 520/533). Reproduce the closure with
`JET_TARGETS='C/jet_secp_wnaf_function5.vo' bash Coq/build-jets.sh -j1` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_wnaf_function5`.
The negative preparation reuses the checked original in-place scalar-negation
call with ownership derived from the real copy. That call allocates and frees
a uint128 local, so the whole function deliberately makes no unchanged
`Mem.nextblock` claim. Existing caller permissions and framing are preserved.
Next: connect the actual split-lambda scalar outputs to these signed input
adapters, then compose the point table and Strauss loop with the literal
scalar-multiplication program.

The next independent multiplication work is the general non-generator path
used by `off_curve_scale`/`off_curve_linear_combination_1`. Inspect existing
candidate endpoints and claim its scope before adding proofs; reuse the
generator and shared point arithmetic where applicable. The external memset
model remains explicit; its linked implementation has not been proved.

The non-generator table calls `gej_double_var(&d, a, NULL)` with distinct
source and destination. The earlier whole doubling proofs were in-place and
cannot justify this call by silently copying the source into the result.
`jet_secp_double_separate_product` proves the actual first multiplication
`d.z = a.z * a.y` with two source fields in one allocation and an initially
uninitialized destination field. It reuses the verified u128 multiplication
oracles and derives its event obligations internally.
`jet_secp_double_separate_prefix.exec_double_separate_prefix` composes the
first five original arithmetic calls, preserving all three source coordinates,
both projective owners and the S/L temporaries, and deriving reusable result
bounds. Its frame now also retains both infinity-flag locations.
`jet_secp_double_separate_middle`, `_tail` and `_body` complete all fifteen
actual arithmetic calls and the real flag copy. `jet_secp_double_separate_function`
proves the whole original `gej_double`, including its three allocations, void
return and all frees. `jet_secp_double_var_separate` adds the original finite
input dispatch, NULL-ratio skip, normalizes-to-zero call and final flag store.
`jet_secp_double_separate_literal.eval_double_var_separate_literal` connects
that complete call to the existing literal Simplicity doubling term when the
represented input infinity flag is false. Source coordinates and source flag,
both projective owners, output bounds, precise framing and readonly globals
are retained. There is no on-curve or nonzero-Y premise and no new external
helper premise. These are checked helper results, not odd-table execution or
additional public coverage.

`jet_secp_ge_zinv_function.eval_ge_set_gej_zinv` now proves the whole original
coordinate-scaling call, including its two allocations, four arithmetic calls,
flag copy, void return and releases. `jet_secp_ge_zinv_literal` connects its
decoded pair to the existing literal Simplicity `zinv` program for arbitrary
residue-matching X/Y/factor words. The factor can be zero; no inverse equation
or curve equation is assumed. Both actual factor layouts are covered: a
40-byte field at offset zero, or Z at offset 80 of an owned 128-byte point.
The result owner size is parameterized (88 bytes or a larger table allocation),
with the affine result starting at offset zero. Source X/Y/flag, factor limbs,
ownership, output bounds, readonly globals and framing of unread source Z and
the remaining table bytes are retained. `jet_secp_affine_gej_product` shares
the X/Y arithmetic layout proof and verified u128 facts; no C substitution,
external helper premise or new axiom is introduced.

Next compose the table's existing constructor calls and new doubling/zinv
calls, then its seven mixed additions, final Z product and nonempty global-Z
pass. `ge_set_xy` and `gej_set_ge` have existing owned execution proofs.
The whole table call remains open; the offset-zero helper above is not a
public multiplication-jet proof. `jet_secp_ge_zinv_indexed_product` now reuses
the generic field-slice multiplication for arbitrary aligned result offsets,
retaining the real table owner. The indexed arithmetic/function/literal modules
compose the unchanged original statement tree, both allocations, flag copy and
all frees, and relate the decoded pair to the same existing literal `zinv`.
The earlier offset-zero results remain available. No curve/inverse equation,
nonzero-factor restriction or new external-helper premise is introduced.

`jet_secp_globalz_indexed_call.exec_globalz_indexed_scale` instantiates that
whole-call result at the actual Scall node in the nonempty global-Z loop for
all eight table positions. It retains the 704-byte table, source temporary,
factor, output bounds, source/destination flags, caller permissions, framing
and readonly globals, and gives the literal Simplicity result. The temporary's
Z field is not assumed initialized: the C caller only writes X/Y/infinity,
and the helper only reads those fields. This proves the indexed call step;
it does not establish its storage premises through the rest of the caller.
`jet_secp_field_slice_accumulate` now proves the original in-place multiply
at arbitrary field offsets, reusing the same verified word log and numeric
bridge as the disjoint-slice result. `jet_secp_globalz_factor_call` proves the
actual indexed factor branch, including the first-iteration skip, and relates
the result to literal field multiplication. `jet_secp_globalz_prepare` proves
the actual typed X/Y copies and finite flag store without requiring tmpa.Z.
`jet_secp_globalz_iteration.exec_globalz_iteration` composes a complete original
iteration for every starting index 1..7: factor branch, machine decrement,
coordinate copies, flag store and literal coordinate scaling, preserving all
four caller allocation owners, output/factor bounds, framing and readonly
globals. It assumes initial table coordinates and factor/ratio storage, not
execution or any desired helper result. These remain internal helper results.
`jet_secp_globalz_loop.exec_globalz_loop` now composes the actual descending
loop through index zero, deriving each iteration's table/factor storage and
bounds and preserving all eight ratios and finite flags. Its `globalz_walk`
records the exact checked limb recurrence; it is an internal execution model,
not a replacement for the canonical public Simplicity program.
`jet_secp_field_slice_weak` reuses the existing normalization carry-pass and
numeric proofs at arbitrary field offsets. `jet_secp_globalz_start` composes
the original last-Y normalization and ratio-to-zs typed copy.
`jet_secp_globalz_function.eval_ge_table_set_globalz_eight` proves the whole
original function for the eight-entry single-point table used by this caller:
both actual local allocations, prefix, all seven iterations, void return and
both frees, exact limb outputs, all ratio fields, both caller owners, old
permissions, unrelated memory and readonly globals. Initial table fields may
be loose within the shared multiplier bounds; no on-curve, nonzero-factor,
inverse equation or external-helper premise is added. Input table flags are
finite, as established by the odd-table constructor calls.
The whole odd-multiple table, its seven indexed mixed additions and the
connection to the canonical `scalarTable5`/`pass2_8` tree remain open; the
whole global-Z execution theorem alone is not public jet coverage. Use the
existing scoped build/kernel/audit commands with the
separate-doubling, ge-zinv and global-Z module names; registry entries here
audit helpers, not new jet coverage.

For the next mixed-addition step, reuse
`jet_secp_mixed_function_loose.eval_mixed_function_xy`, its shared proof-mode
preparation/body modules and `jet_secp_mixed_xy_literal`. They already handle
loose X/Y with actual normalized temporary values and raw-coordinate doubling;
do not reimpose the older ratio function's positioned-X/Y premises on table
outputs. The NULL-ratio callers are complete; the remaining adaptation here
is the non-NULL ratio path at the actual `zr[i]` offset and its array owner.

`jet_secp_double_var_ratio_slice` now covers the complete original finite
`gej_double_var` call with loose raw Y and a ratio output at an arbitrary
aligned slice of a real array owner. The actual copy/weak-normalize calls
write `weak_loose_words y` to that slice, while doubling uses the raw point;
all output bounds, ownership, old permissions, framing and readonly globals
are retained. The earlier positioned-Y/offset-zero proofs remain unchanged.
`jet_secp_field_slice_set` proves the actual `fe_set_int(0/1)` call on such a
slice, without requiring initialized contents or substituting `fe_clear`.
`jet_secp_mixed_equal_ratio_slice` and
`jet_secp_mixed_inverse_ratio_slice.exec_mixed_zero_head_ratio_slice` compose
the original H/I tests and both H=0 outcomes: doubling for I=0, or ratio-zero
initialization and point infinity for I<>0. The ratio and point bounds needed
by subsequent table/global-Z calls are returned; unrelated array entries are
framed. No on-curve or positioned-Y premise is added. These are checked
internal branch results, not a whole-public jet theorem.
`jet_secp_mixed_nonzero_ratio_slice` now composes the actual nonzero-H ratio
copy, H guard, Z/H2 operations, existing private-field products and XY tail
for an arbitrary aligned ratio slice with its full array owner. The existing
verified arithmetic is reused and neighboring ratio entries are framed.
`jet_secp_mixed_finite_ratio_slice.exec_mixed_finite_ratio_slice` executes the
complete original finite-point function body, deriving the normalized
temporaries, H/I, both H outcomes, exact point/ratio limbs, output bounds and
all thirteen owners from initial storage. It supports the existing loose-X
proof mode and loose Y, and retains the affine source's X/Y/finite flag for
the next table iteration. Neither a desired execution nor intermediate H/I
values are assumed. Earlier positioned/offset-zero contracts stay unchanged.
`jet_secp_mixed_infinite_ratio_slice` executes the incoming-infinity branch's
actual ratio clear and affine-to-projective call at the indexed destination.
`jet_secp_mixed_body_ratio_slice` joins it with the finite body without an
assumed intermediate execution. Finally,
`jet_secp_mixed_function_ratio_slice.eval_mixed_ratio_slice_mode` proves the
whole original call, with real entry, ten allocations and ten frees, every
incoming flag, loose coordinates, an aligned ratio slice and its full array
owner. Exact point/ratio limbs and their bounds, affine source fields and
finite flag, caller ownership, old permissions, unrelated memory and readonly
globals are returned. No external-helper or desired-result premise is added.
`jet_secp_odd_table_iteration` composes the original indexed mixed call,
affine table writer and increment for every loop index 1 through 7. Its
result includes the updated accumulator (including its actual infinity
flag), table entry, ratio entry, affine source, bounds, all four owners,
old permissions and the frame outside the selected entries.
`jet_secp_odd_table_loop.exec_odd_table_loop` now proves the complete original
ascending loop, including guards, increments and termination at index 8.
Starting from the initialized prefix and bounded accumulator, it derives
all eight table/ratio fields and bounds, the final accumulator, preserved
affine source, caller ownership, old permissions, unrelated memory and
readonly globals. The exact limb recurrence `odd_table_walk` is an internal
execution result, not a replacement for `scalarTable5`.
`jet_secp_odd_table_head` now derives the first table entry and affine helper
point from the actual distinct-destination doubling and coordinate-scaling
calls, retaining the input and doubled Z even for zero-Y/off-curve points.
`jet_secp_odd_table_seed` composes the actual accumulator constructor and both
typed field copies, deriving the initialized table/ratio prefix and bounded
accumulator without requiring values for unwritten entries.
`jet_secp_odd_table_body.exec_odd_table_body` composes that initialization,
the complete seven-iteration loop and the original final Z multiplication.
It returns exact table/ratio limbs, bounds, accumulator and Z product, the
preserved original input, all seven owners, old permissions, unrelated memory
and readonly globals. No intermediate helper result or library model is an
added premise.
`jet_secp_odd_table_function.eval_ecmult_odd_table_eight` now proves the whole
original helper call for the actual eight-entry caller: three allocations,
parameter binding, complete body, void result and all three frees. It returns
all eight table/ratio entries and bounds, the exact Z product, the preserved
input and all four caller owners, old permissions, unrelated memory and
readonly globals. Initial destination contents need not be initialized.
`jet_secp_mixed_xy_ratio_literal` generalizes the existing ratio bridge to
arbitrary matching bounded loose limbs, retaining every infinity/H/I branch.
The ratio equals the **normalized** literal first projection; the point equals
the literal second projection. It does not claim the refuted raw ratio
equality. `jet_secp_mixed_xy_flag` proves that the actual output flag remains
the zero test of the resulting Z field, using the existing checked field-prime
and multiplication proofs for the nonzero-H case.
`jet_secp_mixed_ratio_slice_literal.eval_mixed_ratio_slice_literal` composes
those results with the original complete indexed-ratio C call, including its
allocations/frees, storage, four output bounds, the resulting flag/Z invariant,
preserved affine input, owners, old permissions, frame and readonly globals.
The incoming flag/Z and residue relations are initial representation premises;
no outgoing relation, helper execution or arithmetic result is assumed.
`jet_secp_scalar_table_literal` ports the fixed `scalarTable5`, `pass1_*` and
`pass2_*` routing, preserving its balanced ratio tree and raw literal ratios.
Its first-pass denotation exposes exactly seven extended additions, with
parametricity proofs for all three first-pass programs.
`jet_secp_odd_table_literal_walk.odd_table_walk_literal` couples the actual C
limb recurrence to those literal additions. Each intermediate bound is derived
from a checked C iteration on the current memory, not supplied as a trace-wide
premise. Initial residue/flag and initialized-prefix relations are preserved.
`jet_secp_odd_table_pass1_bridge.exec_odd_table_pass1_eight` combines that result
with the complete original ascending loop: actual stored entries, their bounds,
accumulator, final index, owners, old permissions, frame and readonly globals,
plus equality of the decoded C array's balanced tree to the normalized field
encoding of `pass1_8`, including its final Z value. Generic tree-map/congruence
lemmas keep arithmetic opaque; point-pair reconstruction and the final Z
projection are explicit, so proof checking need not evaluate the field program.
`jet_secp_table_field_equiv` proves exact multiplication, square, cube and
coordinate-scaling congruence for residue-equivalent words, without canonical
input, on-curve or nonzero-factor restrictions. `jet_secp_scalar_table_pass2`
lifts these facts through the fixed balanced traversal: `literal_pass2_8_normalize`
proves normalization of every ratio and coordinate leaves its complete output
unchanged. `table_pass1_consumed` instantiates that result at the normalized
tree established by the checked first-pass execution theorem. It is a pure
consumer bridge, not yet an execution theorem for the descending C loop.
`jet_secp_globalz_word_walk.globalz_walk_decoded` decodes the checked C
global-Z recurrence (indexed updates, first-iteration skip) into a word-level
walk, deriving every next-state bound from existing arithmetic theorems.
`jet_secp_globalz_pass2.eval_ge_table_set_globalz_pass2` combines it with the
whole original eight-entry call: the decoded final C table equals the balanced
`literal_pass2_8` tree of the decoded inputs. Canonicity of the last ratio and
point follows from field decoding; the weak final Y is handled by
`globalz_start_decoded`. No input words are restricted.
`jet_secp_odd_table_seed_literal.odd_table_initial_literal` now derives the
initial accumulator/prefix and doubled-affine residue relations from the exact
original head/seed word outputs. It uses the caller's finite-input Z/flag
invariant and the initial field relations; no on-curve or nonzero doubled-Z
condition is needed. `literal_scalar_table5_route` exposes the unchanged
program's doubling, first pass, final Z multiplication and second-pass routing.
These are pure bridges, not a new C execution or public coverage entry.
`jet_secp_odd_table_firstpass_literal` now composes those initial relations
with the actual head, seed and seven C iterations. Its caller-level theorem
constructs the private workspace and derives every intermediate bound from
checked execution, rather than assuming a trace or final literal relation.
`jet_secp_scalar_table_execution.eval_scalar_table5_calls` combines the two
whole original C calls (odd-table construction and descending global-Z
adjustment) with the literal first/second passes. It proves that the decoded
final Z product and eight-entry table equal the fixed `literal_scalar_table5`
result. The C allocations/frees, initial representation and ownership, source
fields, final owners, old permissions, frame and readonly preservation are
retained. The finite-input Z/flag condition is the existing caller branch
invariant; no on-curve or nonzero doubled-Z condition is introduced.
The endpoint also retains magnitude-one bounds on every final Y coordinate,
as required by `ecmult_table_get_ge`'s actual `fe_negate(..., 1)` call.
`jet_secp_globalz_tight_y` derives them from the last Y's original weak
normalization and the other seven product outputs, rather than assuming them
at the consumer boundary. Reuse `globalz_multiply_commutes` for the final Z
product's reversed argument order.
`jet_secp_table_get_literal.eval_table_get_lookup5` now executes the whole
original `ecmult_table_get_ge` function for every signed window-5 digit and
proves its decoded point equals the fixed `lookupTable5` combinator port in
`jet_secp_lookup5_literal`. All sixteen nibble cases retain the exact source
bit routing; the operational proof derives C's signed index, 88-byte struct
copy and negative branch's actual magnitude-one `fe_negate` call. The affine
executor is reused at arbitrary table limbs, including weak-normalized Y,
rather than requiring reader-shaped limbs. The result retains exact stored
fields, valid output bounds, flag, owners, old permissions, frame and readonly
preservation. Its table Y premise is supplied by the preceding construction
theorem above; no helper execution or desired output is assumed. Reproduce
with `JET_TARGETS='C/jet_secp_table_get_literal.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_table_get_literal`. This internal lookup adds no public coverage.
`jet_secp_table_get_lambda_literal.eval_table_get_lambda_lookup5` now
executes the whole original `ecmult_table_get_ge_lambda` call and identifies
its decoded point with `lookupTable5 >>> ge_scale_lambda`. The shared signed
index/guard and negative-Y execution are reused; `jet_secp_ge_set_xy_sources`
establishes the actual constructor with independent X-array and Y-table
pointers. It retains the exact field words, output bounds, zero infinity
flag, all three owned regions, old permissions, frame and readonly preservation.
`lookup5_stored_point` factors the common literal selector bridge without
changing the existing ordinary-lookup theorem. Normal compilation and focused
checks use `C.jet_secp_table_get_lambda_literal` as the root.
The lambda endpoint requires the incoming auxiliary X-array to represent
beta times each original X. This is an internal representation invariant,
not a discharged caller obligation or another public jet proof.
`jet_secp_beta_slice.eval_beta_slice_product` now derives each original
`fe_mul` call from a loose stored coordinate, a writable destination slice,
slice separation and the actual initialized read-only beta global. It proves
the exact stored output and its `fe_multiply_beta` decoding, retains the
input coordinate, and preserves beta initialization, old permissions and
readonly memory. Its frame excludes the three represented field slices;
when preserving the source table, use the retained input-field theorem for
the selected coordinate and the frame for the other entries. No complete
helper execution, event solution or beta-product equality is assumed by this
endpoint. `jet_secp_field_slice_borrowed` reuses the original three-slice
executor and checked u128 log with borrowed RHS metadata; `fm_solves`
discharges that log inside the beta caller. Reproduce this closure with
`JET_TARGETS='C/jet_secp_beta_slice.vo' bash Coq/build-jets.sh -j1` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_beta_slice`.
`jet_secp_beta_loop.exec_beta_auxiliary_one` now executes that original
nested auxiliary-array loop for the one-point caller (`no=1`): counter
initialization, eight actual multiplications, inner/outer increments and both exit
tests. The input X coordinates need only the existing loose bounds. Every
product's stored words, bounds and `fe_multiply_beta` relation are derived;
the source table, state pointers, initialized beta global, owners, old
permissions, readonly memory and unrelated loads are retained. Its suffix
invariant is `beta_aux_prefix`; the selected input coordinate is preserved
through each multiply, while the actual frame handles the other table cells.
`jet_secp_beta_lookup.exec_beta_array_then_lookup` composes this complete
array construction with the original signed lambda lookup and identifies
the decoded returned point with `lookupTable5 >>> ge_scale_lambda` on the
original table. It no longer assumes an initialized beta array, any helper
execution or the products' desired values. All sixteen signed window-5
digits are covered. Reproduce this closure using
`JET_TARGETS='C/jet_secp_beta_lookup.vo' bash Coq/build-jets.sh -j1` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_beta_lookup`.
The actual loop is `generator_auxiliary_statement` in
`jet_secp_generator_globalz_call`; the older empty-case theorem covers the
separate `no=0` branch. These internal results add no public jet coverage.
Next compose these calls into the actual Strauss caller, including its scalar
split, signed digit buffers and table consumers. Do not assume raw ratio
equality or replace the fixed program with group scalar arithmetic. The table
call theorem is not a public extended-addition equivalence or a whole
multiplication-jet theorem; coverage remains 520/533.
Check this closure with
`JET_TARGETS='C/jet_secp_scalar_table_execution.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_scalar_table_execution` under the pinned toolchain and stack setting.

For the remaining scalar split-lambda path, reuse
`eval_scalar_mul512_borrowed_product`; the full 512-bit product is already
proved. `jet_secp_scalar_cadd_control`, `_run`, `_body`, `_function` and
`_numeric` now execute the whole original `scalar_cadd_bit(r, 0, flag)` for
both round-bit flags and every four-word input. `eval_scalar_cadd_value`
returns exact scalar storage for `(value + flag) mod 2^256`, including carry
through all four limbs, with actual local allocation/free, retained ownership,
permissions, readonly globals and outside-scalar framing. `cadd_output_exact`
identifies the unwrapped sum when it fits. The four selector arguments are
derived from their actual C expressions; the intervening slices reuse the
existing executor and proved shift-64 oracle. No library model, desired output
or helper execution is a premise. This is an internal helper result; coverage
stays 520/533. Reproduce with
`JET_TARGETS='C/jet_secp_scalar_cadd_numeric.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_cadd_numeric`.
`jet_secp_scalar_shift384_function.eval_scalar_mul_shift384_borrowed` now
proves the whole original `scalar_mul_shift_var(..., 384)`: actual 64-byte
product allocation, the existing full 512-bit multiplication call, original
settings and short-circuit branches, four quotient stores, bit-383 load,
conditional-add call, void return and actual product free. Its exact stored
value is `floor((P+2^383)/2^384)` for the full product `P`; both operands,
destination ownership, caller permissions and readonly globals are retained.
The second operand is readable and non-owned, covering a static multiplier.
The caller supplies a distinct owned destination; these are the actual
split-lambda locals, not a restriction on the public jet input. There is no
assumed product/round value, helper execution, library model or new axiom.
`shift384_output_bounds` proves the generic rounded value is at most `2^128`:
equality is deliberately allowed, so this result never truncates to Word128.
The coefficient-specific strict bounds are established by the following
rounding-prefix result. Reproduce the generic call with
`JET_TARGETS='C/jet_secp_scalar_shift384_function.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_shift384_function`.
The distinct-destination adapters for scalar add and borrowed-RHS scalar
multiply are now available below. Use these for the two calls whose output
pointers differ from both sources; the old in-place contracts do not match.
Reuse the existing owned in-place add, borrowed in-place multiply, scalar
negation and initialized-lambda region proofs where their pointers match.
`jet_secp_scalar_constant` shares the actual-initializer and readonly transport
proof for four-limb scalar constants. `jet_secp_split_multipliers` applies it
to both original `g1`/`g2` globals, checks their Haskell values, establishes
their state from actual `Genv.init_mem`, and proves strict Word128 bounds for
both rounded coefficients on every 256-bit input. No group-order input
restriction is needed for these bounds. `jet_secp_split_round_literal` ports
the exact `roundDivTwo384` term and rounded-coefficient components, with
parametricity and exact integer semantics; the carry is discarded only after
the strict bounds are proved. `eval_split_coefficient_literal` instantiates
the whole original C rounded-product call against each literal component.
`jet_secp_split_rounding_entry.scalar_split_entry_rounding` then derives the
actual `scalar_split_lambda` entry, both fresh coefficient allocations, all
three initial no-op assertions and both original Scall statements. Both exact
literal coefficient stores, retained source and global state, ownership,
freshness, permissions and framing are produced by the prefix. The input and
readonly multipliers are representations, not assumed executions or outputs;
initial program memory establishing the multiplier state is also proved to
exist. These remain internal results; public coverage stays 520/533. Reproduce
with `JET_TARGETS='C/jet_secp_split_rounding_entry.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_split_rounding_entry`.
`jet_secp_scalar_add_separate.eval_scalar_add_separate_values` now executes
the original scalar add into a distinct destination with unrestricted initial
contents, retaining both source scalars and all three owned allocations. Its
symbolic run proves that the actual result uses exactly the existing in-place
carry/reduction expressions, so it reuses the modular-sum and overflow proofs
instead of duplicating them. For each pair of scalars below the group order,
it returns the exact modular sum and overflow flag, permissions, readonly
preservation and outside-object framing. This supplies the `r2=c1+c2` call
shape of split-lambda; no helper execution, result or output initialization is
assumed. Reproduce with
`JET_TARGETS='C/jet_secp_scalar_add_separate.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_add_separate`.
It is internal support and adds no public coverage (520/533).
For distinct-destination multiplication, use
`jet_secp_reduce512_fresh_function.eval_reduce512_fresh_storage`, not
`eval_reduce512_numeric_owned_loads`: the older entry representation requires
four initialized destination words. The fresh contract now derives the
complete original reduction call from uninitialized destination cells and the
eight actual source limbs. Its first two stages establish the same arithmetic
checkpoints without reading the destination; the third performs the original
four writes and rejoins the existing initialized final suffix. It returns exact
canonical storage of the 512-bit input modulo the group order, the retained
source representation, ownership, permissions, readonly preservation and
framing. There is no initial destination load, helper execution, arithmetic
result or new library-model premise. Existing first/second/third-fold and
final-reduction arithmetic are reused unchanged. All stages, function entry,
local allocations and frees are derived. Reproduce with
`JET_TARGETS='C/jet_secp_reduce512_fresh_function.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_reduce512_fresh_function`.
`jet_secp_scalar_mul_separate.eval_scalar_mul_borrowed_separate` now composes
the complete original scalar-multiply call with a distinct uninitialized
destination and a readable non-owned second operand. It derives the actual
64-byte product allocation, full borrowed-input 512-bit multiplication,
product-to-fresh-reduction representation, original two Scalls, return and
product free. Both input representations, destination ownership, permissions,
readonly globals and outside-object framing are retained. Its result is the
exact product modulo the group order, not a supplied arithmetic output.
`eval_scalar_mul_separate_values` exposes that call from two actual scalar
stores for every pair of 256-bit values; only the first operand and destination
need caller ownership. This matches `r1=r2*lambda` in split-lambda and adds no
initial destination contents or library-model premise. Reproduce with
`JET_TARGETS='C/jet_secp_scalar_mul_separate.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_mul_separate`.
These are internal call contracts; public coverage remains 520/533.
`jet_secp_split_function.eval_scalar_split_lambda` now derives the complete
original split-lambda call: entry, the two fresh coefficient objects, the three
initial no-op assertions, both rounded products, both basis multiplications,
the distinct-destination second-result addition and lambda multiplication,
negation, final addition, return and both actual frees. The exact C outputs are
`split_first_value k` and `split_second_value k`. Both caller output objects
have unrestricted initial contents; neither private coefficient, intermediate
execution, arithmetic output nor initial output load is a premise. The five
original readonly globals (g1, g2, minus_b1, minus_b2 and lambda) are established
at actual program initialization and preserved. The original input, all three
caller-owned allocations, readonly state, permissions and outside-object frame
are retained. The internal input scalar is canonical, as established by the
existing public readers; this is not a restriction on public Word256 inputs.
The numeric in-place interfaces reuse the existing multiplication, negation
and addition executions and arithmetic. Reproduce the new closure with
`JET_TARGETS='C/jet_secp_split_function.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_split_function`.
This theorem proves C execution and its exact modular values; its subsequent
literal signed-half composition is recorded below. Public coverage remains
520/533.
`jet_secp_split_signed_bounds` now proves the actual rounded-coefficient error
intervals, both strict signed 128-bit bounds, and the fixed lattice residue
identities. For the two coefficients c1/c2, the signed values are
`k-b2*c1-a2*c2` and `minus_b1*c1-b2*c2`; the modular values computed by C are
proved to be exactly their residues modulo the group order. The bound proof
uses linear arithmetic on the original fixed constants and rounding errors;
every theorem in this arithmetic module is closed. No small-output or lattice
fact is assumed. `jet_secp_split_small.eval_scalar_split_lambda_small` composes
those facts with the entire original C call, producing both exact stores,
strict signed ranges and the complete input/ownership/frame postcondition.
Reproduce with `JET_TARGETS='C/jet_secp_split_small.vo' bash Coq/build-jets.sh -j1`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_split_small`.
This is still internal support and does not add public coverage (520/533).
The exact signed bit/word bridge is now complete in
`jet_secp_split_literal_function.eval_scalar_split_lambda_literal`: it returns
the exact `wnaf5_input_scalar` of each literal half, rather than only a
group-order congruence. See the current scalar-multiplication milestone at the
end of this file. Reuse it instead of rebuilding the original calls or adding
output/phase premises. The remaining public path needs the original
Strauss caller and loop composition.
Build the helper with `JET_TARGETS='C/jet_secp_odd_table_function.vo' bash
Coq/build-jets.sh -j1`, then recursively kernel-check it with `bash
Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_odd_table_function` under the pinned toolchain and stack setting.

`jet_secp_ge_set_xy_indexed` proves the whole original affine constructor at
any valid aligned result offset, retaining exact permission equivalence and
framing outside that entry's 84 written bytes. `jet_secp_odd_table_write` applies
it to the actual original loop call for every `0 <= i < 8`, retaining the full
704-byte table owner and framing other entries. This closes the indexed
constructor/writer step, not the mixed-addition step or the whole loop.

For subsequent indexed arithmetic, `jet_secp_field_slice_product` proves the
original `fe_mul` on three arbitrary aligned disjoint 40-byte field slices;
the slices can share an allocation. It derives the u128 event obligations,
concrete limbs, numeric result and bounds from initial storage. Ownership at
offset zero is not required: `jet_secp_slice_permissions` reuses the already
existing `jet_clight_internal_permissions` theorem and the checked original
internal call table to retain every initial permission, including Freeable.
This does not change the execution model or assume a helper result. Reuse
these facts to generalize indexed ratio/result destinations rather than
adding more fixed-offset multiplication layouts. The initial writable-field
and pairwise slice-separation premises must be discharged at callers; this
three-region result does not cover an output aliasing an input.

The independent scoped kernel roots for this batch are
`C.jet_secp_field_slice_product` and `C.jet_secp_odd_table_write`; check both
with the existing `build-jets.sh --coqchk` command. Public coverage is unchanged.

`jet_secp_wnaf_literal_values` proves every reachable literal `Some` digit
is odd and nonzero in the signed range, zero C integers correspond exactly
to `None`, and equal C integers uniquely determine the raw literal digit.
All ten exports are closed. This discharges the raw-constructor distinction
lost by numeric decoding; it is not additional public-jet coverage. Normal
build, recursive kernel checking and focused no-update assumption/contract
comparisons pass; use the commands below with this module name.

A subsequent read-only Astra Medium review recommends the original
`fe_from_storage` / `ge_from_storage` execution next, then signed
`ecmult_table_get_ge_storage`. Use **readable**, not owned writable, source
storage: both frozen generator tables are readonly. The desired decoder
endpoint takes eight source Mint64 words and a disjoint writable affine
destination, derives the exact five-limb coordinate unpacking and infinity=0,
and preserves source/permissions/framing. Reuse `jet_secp_signed62_repack`,
`jet_secp_affine_fields` and `jet_secp_field_copy_owned` patterns, without
inheriting their writable-source premises where inappropriate.

`jet_secp_storage_unpack.eval_fe_from_storage_readonly` now derives the
original field decoder's execution from arbitrary four-word readable storage
and a disjoint, aligned writable destination slice. It writes the exact five
machine words, preserves source typed loads/readability, and frames outside
the **union** of both regions. It does not yet establish arbitrary-chunk
source framing or equality of all permissions. Its source is not required
writable or Freeable; its destination need not start at offset zero.
`jet_secp_storage_numeric` proves exact integer preservation, canonical limb
bounds and agreement with the existing normalizer for every four-word input.
All seven arithmetic exports are closed; execution retains only the six
inherited assumptions, with no new library model. Normal build, recursive
kernel checking and reviewed no-update focused assumption/contract comparisons
pass for both modules (use the commands below with their module names).
This is helper progress, not additional accepted coverage.

`jet_secp_affine_storage.eval_ge_from_storage_readonly` composes the actual
two field-decoder calls and infinity assignment. It derives execution from
arbitrary readable source64 and a distinct owned destination88, retains
destination Freeable ownership, preserves all eight source typed loads and
exposes exact coordinate limbs and infinity=0. The coordinate arithmetic
adapter is closed. Normal build, recursive kernel checking and reviewed
no-update focused assumption/contract comparisons pass. Its base contract
still frames outside the union of the regions.

`jet_secp_affine_storage_frame.eval_ge_from_storage_table` now restores full
table-block framing using the existing general Clight readonly readback
theorem. Given the source block's actual readonly permission bounds, it
derives the original decoder's execution, retains those bounds exactly and
frames arbitrary chunk loads and permissions outside destination bytes
[0,84), including the source block and untouched destination padding. It
does not assume table coordinate correctness. The footprint lemma is closed;
the framing/combined exports use eight standing inherited assumptions,
including CompCert's external-call and inline-assembly properties through
the general readback theorem (the base execution exports use six).
Normal build, recursive kernel checking and reviewed no-update focused
assumption/contract comparisons pass. Reproduce this decoder chain with
Coq 8.17.1 and prepared dependencies:

```sh
JET_TARGETS=C/jet_secp_affine_storage_frame.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_affine_storage_frame
```

The signed lookup's two reusable phases are now checked:
`jet_secp_table_index` derives the actual signed C division and scaled pointer
addition with index `(abs n-1)/2` in [0,8192) for 0<abs n<16384.
`jet_secp_table_decode.eval_table_decode_signed` derives the decoder and,
for a negative digit, the actual magnitude-one field negation. It retains X,
infinity=0, owned destination88, all source typed loads, readonly permission
bounds and full framing outside the written destination84. No normalized-
coordinate or generator-table correctness fact is assumed. Normal builds,
recursive kernel checks and reviewed no-update focused assumption/contract
comparisons pass. The pure arithmetic adapters are closed; expression
execution uses four inherited assumptions and combined table execution uses
the same eight standing assumptions as the readonly decoder. These phases
are not a public `generate` theorem or additional coverage.

`jet_secp_table_call.eval_ecmult_table_get_ge_storage` now derives the whole
original lookup call at the generator caller's width15: entry, all three
original assertion loops, signed branch/index computation, original decoder,
optional original Y negation, void return and empty-local release. It accepts
every 0<abs n<16384 (in particular every reachable nonzero wNAF15 digit), with
the selected eight readable words and actual readonly block bounds. No helper
call, desired coordinate, execution or intermediate memory is an input
premise. It retains exact signed-coordinate machine limbs, infinity=0,
destination ownership, source loads, readonly bounds and full external
framing. Normal build, recursive kernel checking and reviewed no-update
focused assumption/contract comparisons pass; its combined endpoint uses the
same eight standing inherited assumptions as the table decoder. Reproduce:

```sh
JET_TARGETS=C/jet_secp_table_call.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_table_call
```

`jet_secp_generator_globals` now derives both tables' original symbol/variable
bindings, 65536 Init_int64 words, size524288, every typed load and exact
readonly permission bounds from `Genv.init_mem jets_secp.prog`. The generic
initializer proof traverses the list structurally; count bounds use Z, not
large unary nat constants. Symbol lookup uses conversion without expanding
the table payload. Do not replace it with broad `vm_compute` on variable
records. Normal compilation needs no increased stack limit.

`generator_tables_initialized_memory_exists` proves a real initial memory
for both tables, reusing the existing frozen-program initialization proof.
`eval_generator_table_lookup` instantiates the complete original lookup with
the selected actual initializer words and preserves the whole table state.
`generator_table_lookup_fresh` derives initialization, a fresh owned88
allocation and the lookup for every 0<abs n<16384 and either table, with
exact signed-coordinate output, infinity=0 and framing. It assumes neither
table values nor frame/source/environment relations. This establishes actual
table execution, **not** equality with a literal generator program. Metadata
proofs are closed, memory/initialization facts use four inherited assumptions
and execution uses the same eight as the readonly lookup. Normal build,
recursive kernel check and reviewed no-update focused assumption/contract
comparisons pass. Reproduce:

```sh
JET_TARGETS=C/jet_secp_generator_globals.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_globals
```

The two 8192-entry table bridges to the exact literal `generateSmall` /
`generate128Small` results are now proved for every signed digit (see the
exhaustive certificate and lookup results below). The original
`gej_add_zinv_var` call at represented inverse-Z one also has a checked literal
coordinate bridge. Remaining: establish that inverse field through the real
caller and align C's shortened descending loop with the literal 129 steps.
Maintain field congruence and limb bounds internally, but discharge exact
normalized coordinate equality at the writer boundary, not only projective
point equivalence. No table-correctness assumption is authorized.

The subsequent readonly Astra Medium strategy review identifies literal
normalization as a separate missing implication: Haskell's `gej_norm` calls
`fe_invert`, which calls the actual `Arith.bezout word256` term. A modular
inverse witness alone does not connect to that program. Next port the exact
EEA step, structural iteration and coefficient extraction, then prove a
numeric simulation or correctness/bounds/uniqueness bridge; benchmark a
small checked certificate before scaling. Reuse the existing literal division
bridge (`jet_literal_division_add.literal_div_mod_matches` and
`jet_division_result_spec.div_mod_word_numeric`), word multiplication and
comparison proofs, and the exact doubling/mixed-add literal step lemmas.
Share the signed binary recursion/prefixes explicitly and retain all infinity
and exceptional branches. Prove both signed paths rather than assuming
negative scalar multiplication commutes with normalization. The second base
is already a fixed literal `generate128` constant (LibSecp256k1.hs:454);
proving it equals 2^128 G is not required for this exact literal bridge.
Neither this strategy review nor the completed initialization proofs establish
that semantic bridge or increase public-jet coverage.

The first EEA step is now complete in `jet_secp_eea_literal` and
`jet_secp_eea_numeric`: a structural port of the actual row update, comparison
branch, doubled iteration, zero/one initialization and signed coefficient
extraction, together with `literal_bezout_numeric` for every word width and
every input pair. It derives the exact numeric run (512 steps at word256),
including coefficient wrap modulo the word modulus, division-by-zero behavior
and the output sum constructor. It does not replace the literal computation
with an assumed inverse or a mathematical gcd specification. All seven
structural exports are closed; numeric simulation uses only the existing
functional-extensionality assumption through the literal division adapter.
Normal build, recursive kernel check and reviewed no-update focused
assumption/contract comparisons pass. Reproduce:

```sh
JET_TARGETS=C/jet_secp_eea_numeric.vo bash Coq/build-jets.sh -j1
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_eea_numeric
```

`jet_secp_invert_literal` now connects the exact Haskell field-inversion
wrapper to that evaluator. `literal_fe_invert_numeric` and
`literal_fe_invert_word` hold for **every** Word256 input and preserve the
signed coefficient selection: the left branch negates its second coefficient
modulo the field order, while the right branch returns its actual second
word without adding a normalization that is absent from the specification.
The closed numeric checks for inputs0,1,2 reduce in roughly 0--0.11 seconds
locally, and the lifted word equalities are checked. This is a small evaluator
benchmark, not a complete table certificate or a general inverse-uniqueness
theorem. Normal build, recursive kernel checking and reviewed no-update
focused assumption/contract comparisons pass. Generic selection, routing and
numeric sample certificates are closed; whole-program numeric/word bridges
use only inherited functional extensionality. Reproduce with target/module
`C/jet_secp_invert_literal.vo` / `C.jet_secp_invert_literal` as above.

Avoid a conversion proof that compares pattern matching on an unknown
coefficient pair with `snd`: that can force evaluation of the entire literal
EEA. The generic `literal_inverse_body_fun` proves this routing once by
destructing symbolic coefficients, without reducing the actual program.
`jet_secp_eea_parametric` now proves the EEA, Bezout and inversion programs
algebra-independent at every width; all ten exports are closed.
`jet_secp_gej_norm_literal` reuses the existing literal `zinv` tree and proves
the exact numeric and Word256-pair outputs of the literal `gej_norm`, for
arbitrary coordinate words, through the checked numeric inverse evaluator.
Its structural/algebra-independent exports are closed; its numeric/word
bridges use only inherited functional extensionality. No nonzero-Z, curve or
canonical-coordinate premise is introduced. Normal compilation, recursive
kernel checking and reviewed no-update focused assumption/contract comparisons
pass. Reproduce with target/module `C/jet_secp_gej_norm_literal.vo` /
`C.jet_secp_gej_norm_literal` as above (its dependency closure includes the
EEA-parametric module).

`jet_secp_generate_literal` now ports the exact `scaleConstant`,
`generateSigned` / `generate128Signed` recursion and both literal affine bases,
with `generateSmall` / `generate128Small` selected by a bool. The structural
evaluation bridge is proved for every word width, preserving the high-half
before low-half processing and the negative sign-bit initialization; it does
not assume negation commutes with point arithmetic. All eight exports,
including the algebra-independent term proofs, are closed. Normal build,
recursive kernel checking and reviewed no-update focused assumption/contract
comparisons pass. Reproduce with target/module
`C/jet_secp_generate_literal.vo` / `C.jet_secp_generate_literal` as above.
`jet_secp_generator_point_numeric` now derives exact numeric doubling and
mixed-addition from the existing literal step lemmas, retaining infinity and
both H/I exceptional branches, the actual halve behavior, and all raw input
words. `jet_secp_generate_numeric` composes them with the signed recursion
and literal EEA-based normalization. Its final numeric and word theorems hold
for **every** raw Word16 input and either literal base. This is not a
mathematical scalar-multiplication replacement.

`jet_secp_eea_fast` proves an evaluator-only early return: a valid state with
a zero remainder is a fixed point of the exact EEA step, so the remaining
iterations cannot change it. All six optimization exports are closed.
`literal_generate_small_fast_word` discharges its nonnegative-Z condition
through the original word-level program; no precondition is added for callers.
The point/generator bridges use at most inherited functional extensionality;
the structural mixed step and zero-test bridges are closed. Normal compilation,
recursive kernel checking and reviewed no-update focused assumption/contract
comparisons pass for all three modules. Reproduce with target/module
`C/jet_secp_generate_numeric.vo` / `C.jet_secp_generate_numeric` as above;
its closure includes both supporting modules.

`jet_secp_generator_table_samples` now proves exact literal word equalities
for the actual first two frozen entries, for both signs and both tables
(digits +1,+3,-1,-3). Its numeric certificates are closed; its literal lifts
use only inherited functional extensionality. These eight cases are **not**
an exhaustive table certificate or a public C `generate` theorem.

`jet_secp_generator_bits` derives serial bit-fold evaluation and exact unsigned
bit values from the existing signed recursion at every width.
`jet_secp_generator_prefix.generator_prefix_values_lookup` proves the shared
prefix evaluator's indexed result for **every** bit path of its depth. Each
node computes one double and shares it across its zero/one continuations;
negative prefixes retain their exact Jacobian state. All ten bit/prefix
exports are closed. Normal compilation, recursive kernel checking and
reviewed no-update focused assumption/contract comparisons pass for these
three modules. Reproduce the combined closure:

```sh
JET_TARGETS='C/jet_secp_generator_prefix.vo C/jet_secp_generator_table_samples.vo' bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_prefix C.jet_secp_generator_table_samples
```

Next traverse the initializer structurally in eight-word rows (prove complete
length and indexed correspondence), connect the signed bit-prefix ordinal to
the actual table index, and certify both complete tables. Avoid repeated large
`nth` lookups. Exploratory shared-prefix blocks show that direct literal EEA
evaluation is still expensive: a four-entry block passed for both signs/bases,
but a sixteen-entry negative block exceeded the ten-second exploratory limit.
Do not launch the full table sweep without addressing that measured cost.

A useful next optimization is a proved inverse bridge for the **actual** EEA
run on canonical nonzero Z, then table-leaf checks by nonzero Z, canonical
table-coordinate bounds and rescaled-coordinate equalities. This avoids
evaluating an entire Bezout run at every leaf, but requires a real EEA proof,
not an assumed inverse: initial rows satisfy `a*p-b*z=c`, `d*p-e*z=-f`,
`a*f+d*c=z` and `b*f+e*c=p`. Prove preservation, coefficient bounds (hence
no word-wrap), termination within the actual 512 steps and coefficient
selection/range; reuse the checked field-prime result for inverse uniqueness.
The existing exact numeric evaluator and small samples remain valid if this
optimization is developed; do not replace the frozen literal term.

The first algebraic part is now checked in `jet_secp_eea_coefficients` and
`jet_secp_eea_remainders`. Coefficient bounds and both signed linear/
conservation identities are preserved by every **actual** modular row update
and run length, proving that the low-word coefficients do not wrap on positive
bounded inputs. The remainder projection preserves gcd (also at zero
denominators); every two steps halve its minimum. `eea_run_finishes` derives a
zero remainder after `2*bits` steps whenever the initial minimum is below
`2^bits`, so the literal 512-step budget is sufficient for 256-bit inputs.
All 23 exports are closed. Normal compilation, recursive kernel checking and
reviewed no-update focused assumption/contract comparisons pass. Reproduce:

```sh
JET_TARGETS='C/jet_secp_eea_coefficients.vo C/jet_secp_eea_remainders.vo' bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_eea_coefficients C.jet_secp_eea_remainders
```

`jet_secp_invert_modinv` now discharges final coefficient selection and range
from those invariants, termination and gcd preservation. Its whole-run helper
assumes only bounded positive inputs and coprimality, not an intermediate
execution or output. The fixed-field bridge discharges coprimality using the
already checked field-prime theorem, handles zero and the field-order value,
and proves `literal_fe_invert_modInv` for **every** Word256 input. The right
branch's returned raw coefficient is proved below p; it is not silently
normalized in the program. Six arithmetic exports are closed; the final
word-program bridge uses only inherited functional extensionality. Normal
build, recursive kernel checking and reviewed no-update focused
assumption/contract comparisons pass. Reproduce with target/module
`C/jet_secp_invert_modinv.vo` / `C.jet_secp_invert_modinv` as above.

`jet_secp_generator_normalization_check` now proves sound rescaled-coordinate
certificates for the exact literal normalization. Its checker verifies the
Z-word bound, nonzero field Z, canonical table coordinates and both rescaled
equalities; inverse correctness is derived from the actual EEA bridge, not
assumed. `jet_secp_generator_prefix_check` proves successful exact consumption
of a prefix block equals the existing literal-normalized value list, with no
skipped branches or unconsumed rows. `jet_secp_generator_rows` traverses the
actual initializer once in eight-word rows, proves complete payload/8192-row
length and indexed equality with every existing table word/numeric value.
`jet_secp_generator_block16` checks the first sixteen actual entries for
both signed paths and both bases (64 cases), and derives their exact existing
prefix-value lists. It is explicitly a block sample, **not all table entries**.
All fifteen arithmetic/decoder/checker/block exports are closed; the two
literal normalization-word lifts retain only inherited functional
extensionality. Normal builds, recursive kernel checking and reviewed
no-update focused assumption/contract comparisons pass. Reproduce the batch:

```sh
JET_TARGETS='C/jet_secp_generator_prefix_check.vo C/jet_secp_generator_rows.vo C/jet_secp_generator_block16.vo' bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_prefix_check C.jet_secp_generator_rows C.jet_secp_generator_block16
```

Next scale to both complete signed tables and connect the bit-prefix ordinal
to every valid raw wNAF digit/table index. The improved 128-entry scratch block
passed for both signs at roughly eighteen seconds each; direct Z.modulo field
evaluation is now the measured scaling cost, not inversion or repeated table
indexing. A verified evaluator-only pseudo-Mersenne reduction (equal to
ordinary modulo for **all** integers, retaining a fallback) can accelerate
these checks without changing the original numeric/literal programs or C.
Keep the proof of point/checker equivalence when adding such an evaluator;
do not treat benchmark success as a complete table certificate.

That evaluator is now checked in `jet_secp_generator_fast_{field,points,check}`.
The fold/clip/fuel-bounded reduction equals Z.modulo for **every** integer;
negative and large values retain total behavior via a fallback. The point,
bit-fold and complete prefix-checker functions are proved exactly equal to
the existing numeric evaluators for all inputs, including every exceptional
branch. This changes no C, literal term, generation configuration or admitted
input domain. All nineteen exports are closed. Normal build, recursive kernel
checking and reviewed no-update focused assumption/contract comparisons pass.
Reproduce with target/module `C/jet_secp_generator_fast_check.vo` /
`C.jet_secp_generator_fast_check` as above. A scratch first-128-entry check
using this evaluator passed for both signs, about 3.4--4.4 seconds per case
locally; this measurement is not an all-table certificate.

The next certificate should use depth13, the exact two-bit signed seed
`[neg;neg]`, and **all** 8192 decoded rows (reverse the rows for the negative
path). Prove the valid raw wNAF digit's two equal top bits, thirteen middle
bits and final odd bit, then relate its middle-bit ordinal to the original
signed table index. Complete checks are required for both signs and both
bases. The full original generator call and external ctz/memset boundaries
remain separate from these table certificates.

`jet_secp_generator_digit_shape` now derives the exact signed prefix shape
from the **existing** raw digit's odd/range invariants; it is not an extra
prefix-shape restriction. `jet_secp_generator_tables_check` defines the full
depth13 checks and proves `generator_tables_match_digit`: given the two full
checker results for a base, every valid raw wNAF15 digit's literal result is
the selected actual frozen table entry, with the original C sign test and
`(abs n-1)/2` index. Negative rows are reversed with a proved indexed lookup.
Eight exports are closed; the two literal-word bridges retain only inherited
functional extensionality. Normal build, recursive kernel check and reviewed
no-update focused assumption/contract comparisons pass. Reproduce with
target/module `C/jet_secp_generator_tables_check.vo` /
`C.jet_secp_generator_tables_check` as above.

The four exhaustive results are now checked in the separate
`jet_secp_generator_table_{g,g128}_{positive,negative}` modules: every one of
the 8192 actual rows for each base and sign, with complete consumption.
`jet_secp_generator_tables_certificates.generator_tables_checked` is closed;
`generator_tables_literal_digit` discharges the former checker premises for
every valid raw wNAF15 digit and retains only inherited functional
extensionality. Separate modules cache the costly checked computations.
Keep `generator_tables_check` locally opaque when assembling these proofs:
ordinary conversion otherwise needlessly unfolds the entire tables. This is
a proof-reduction strategy, not a changed checker, target or kernel setting.

`jet_secp_generator_table_bounds` derives canonical storage-coordinate bounds
from a successful full check. `jet_secp_generator_lookup_words` identifies
the **actual** decoded/optionally-negated machine limbs, proves their
residues and reusable writer/multiplication/squaring bounds. Negative Y stays
the actual loose C value, not substituted canonical limbs.
`jet_secp_generator_lookup_literal.eval_generator_lookup_literal` derives the
complete original signed storage-lookup call and its exact literal-coordinate
field values, infinity flag, ownership and framing. Its endpoint has no
checker-result or intermediate-execution premise; the closed certificates
discharge those internal bridge premises. Its caller variant preserves both
readonly tables and the entire destination allocation of any size >= 88.
Execution retains the same eight inherited assumptions as the existing
readonly-table lookup proof, with no extra libc model.

Normal builds, recursive kernel checking and reviewed no-update focused
assumption/contract comparisons pass. Reproduce the complete table/lookup
closure:

```sh
JET_TARGETS=C/jet_secp_generator_lookup_literal.vo bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_lookup_literal
```

Next compose actual wNAF initialization/calls, the original
`gej_add_zinv_var` at the caller's inverse-Z value one, the descending loop,
and the public writer. For iterative point arithmetic, do not impose the old
mixed-preparation theorem's positioned-X premise on loose C outputs:
`exec_mixed_copy_weak_loose` already supports both X and Y. Also retain the
actual operand order of the initial `az = a->z * bzinv` call; the existing
`eval_gej_z_product_owned` proves the opposite pointer order, so arithmetic
commutativity alone is not an execution adapter.

These stages establish the table/literal correspondence and complete lookup
helper, not public `generate`, the C inversion jet or the external ctz/memset
obligations. Accepted coverage remains 505/533.

`jet_secp_wnaf_return_length` now derives the exact leading-zero prefix that
the original C return length omits from the already-proved literal 129-digit
vector. This follows from the existing `wnaf_last`/array invariant, including
the all-zero input; it adds no input restriction. The two pure list lemmas
are closed; the memory-invariant corollary retains the four inherited
logical assumptions of that invariant. Normal compilation, recursive kernel
checking and reviewed no-update focused audits pass. Reproduce using target
`C/jet_secp_wnaf_return_length.vo` and kernel module
`C.jet_secp_wnaf_return_length`. The actual descending C loop and its
point-arithmetic calls remain to be composed.

`jet_secp_zinv_z_product.eval_zinv_z_product_owned` now proves the actual
initial multiplication's operand order: projective Z at offset 80 first,
the inverse-Z field second, and a fresh 40-byte destination. It derives the
original function call, actual product words/value/bounds, preservation of
both inputs and ownership, and outside-result framing using the existing
proved u128 oracles. `jet_secp_zinv_initial_products` ties the `az` and `z12`
statements to the frozen `gej_add_zinv_var` body and derives each original
assignment from owned storage and machine bounds. These are **separate
prefix-statement proofs**, not yet their sequential/whole-helper composition.
The executions retain six inherited assumptions, without an extra oracle or
libc premise; six structural/source exports are closed. Normal compilation,
recursive kernel checking and reviewed no-update focused audits pass:

```sh
JET_TARGETS=C/jet_secp_zinv_initial_products.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_zinv_initial_products
```

`jet_secp_zinv_product_prefix.exec_zinv_first_products` now joins the initial
multiply and square from one initial memory, including preservation of the
square destination before initialization, both actual output words, residues,
machine bounds, input fields, allocation ownership and framing. Its statement
prefix uses the existing continuation-composition interface.
`jet_secp_zinv_coordinate.exec_zinv_coordinate` proves one shared
copy/weak-normalize/affine-product triple for either X or Y. Both raw point
coordinates may be loose (limbs <= 2^60); the actual changed normalized words
and their tight bounds/residue are retained. No positioned-X assumption or
intermediate execution is introduced. Execution retains six inherited
assumptions; the tight-to-square bound adapter is closed. Normal builds,
recursive kernel checking and reviewed no-update focused audits pass:

```sh
JET_TARGETS='C/jet_secp_zinv_product_prefix.vo C/jet_secp_zinv_coordinate.vo' bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_zinv_product_prefix C.jet_secp_zinv_coordinate
```

`jet_secp_zinv_shared_preparation.exec_zinv_shared_preparation` now joins both
triples into the six original preparation statements. The closed source
lemma identifies their exact continuation in `gej_add_zinv_var`; execution
preserves the raw point/affine fields, all seven allocations, the actual
normalized U1/S1 and multiplied U2/S2 fields, bounds and framing. It retains
six inherited assumptions, not an intermediate execution premise. Normal
build, recursive kernel checking and reviewed no-update focused audits pass;
reproduce with target/module `C/jet_secp_zinv_shared_preparation.vo` /
`C.jet_secp_zinv_shared_preparation` as above.

The final S2 multiplication uses local `az`, not `a->z`. Its proof reuses
the already-proved 40-byte in-place `eval_field_pair_multiply`, rather than
giving a 40-byte temporary a fictitious larger allocation or reproving
multiplication.
`jet_secp_zinv_s2.exec_zinv_s2_az_from_owned` now derives that actual final
assignment using the existing multiplier. Its closed source lemma identifies
the exact continuation. The result retains the actual `field_pair_product`
words, input az, both 40-byte ownership ranges, product residue, tight output
bounds and framing. Execution retains six inherited assumptions. Normal
build, recursive kernel checking and reviewed no-update focused audits pass;
reproduce with target/module `C/jet_secp_zinv_s2.vo` /
`C.jet_secp_zinv_s2`. Sequential composition with the preparation block is
now proved by `jet_secp_zinv_preparation.exec_zinv_preparation`: all seven
original statements after az/z12 execute from their initial represented
fields, deriving all four U/S results, their tight downstream bounds, the
actual S2 triple-product residue, all eight allocation permissions and
framing. A closed source lemma identifies the complete seven-statement
continuation. Execution retains six inherited assumptions. Normal build,
recursive kernel checking and reviewed no-update focused audits pass;
reproduce with target/module `C/jet_secp_zinv_preparation.vo` /
`C.jet_secp_zinv_preparation`. That internal boundary's initial az/z12 fields
are discharged by the following product-prefix composition.

`jet_secp_zinv_start.exec_zinv_start` now joins **all nine original finite-path
preparation statements** from the caller inputs. It requires the represented
input point, affine point and inverse-Z field plus ownership of six writable
private fields, not any initialized temporary, expected output or helper
execution. It derives all twelve field views, nine allocation permissions,
six tight machine bounds and framing, with a closed exact-source continuation
lemma. The registered definitions spell out every field/permission/bound in
the reusable postcondition; no output is hidden as an extra premise.
Execution retains six inherited assumptions. Normal build, recursive kernel
checking and reviewed no-update focused audits pass:

```sh
JET_TARGETS=C/jet_secp_zinv_start.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_zinv_start
```

`jet_secp_zinv_differences` reuses `exec_mixed_differences` for the following
four original H/I statements on the derived tight U1/U2/S1/S2 words.
`exec_zinv_difference_prefix` now composes **all thirteen original statements**
from the six caller fields and writable temporary storage. No initialized H/I
or intermediate execution premise is required. It preserves all input and
preparation field views, eleven allocations, exact H/I radix values, their
square-input bounds and framing. Both source identities are closed; execution
retains six inherited assumptions. Normal build, recursive kernel checking
and reviewed no-update focused audits pass; reproduce with target/module
`C/jet_secp_zinv_differences.vo` / `C.jet_secp_zinv_differences` as above.
This is helper progress, not new accepted public coverage (still 505/533).

`jet_secp_zinv_zero` now derives the actual H/I tests and both H=0 early
returns, including zinv's literal NULL doubling argument (not the older
mixed-addition helper's `_rzr` temporary). The H=0/I=0 path reuses the original
owned doubling call; H=0/I!=0 reuses the original infinity initializer. Raw
point fields, square-input bounds, the finite flag and owned H/I storage
suffice: neither test nor branch execution is assumed. The nonzero-H guard
is also derived. Exact coordinate words, flags, downstream bounds, allocation
ownership and framing are retained. Three source identities are closed;
execution retains six inherited assumptions. Normal build, recursive kernel
checking and reviewed no-update focused audits pass; reproduce with
target/module `C/jet_secp_zinv_zero.vo` / `C.jet_secp_zinv_zero` as above.
These are post-preparation control results, not the full helper or public jet.

`jet_secp_zinv_nonzero.exec_zinv_nonzero_tail` now derives the entire original
nonzero-H continuation: the H test, flag clear, actual Z-first multiplication,
H square, H2 negation, H3/T products and final X/Y writes. Its source equality
shows that after zinv's three start statements, the continuation is exactly
`mixed_after_h_square`. The reusable
`jet_secp_mixed_after_square.exec_mixed_after_h_square` composes existing
`exec_mixed_products` and `exec_mixed_xy_tail` rather than reproving arithmetic.
Exact output words, flag, square-input bounds, all eight allocations and
framing are retained, with no initialized private output or execution premise.
Two source identities are closed; execution retains six inherited assumptions.
Normal builds, recursive kernel checking and reviewed no-update focused audits
pass; reproduce with targets/modules `C/jet_secp_mixed_after_square.vo` and
`C/jet_secp_zinv_nonzero.vo` / their `C.*` module names as above.

`jet_secp_zinv_finite.exec_zinv_finite_body` now composes the thirteen-statement
prefix, both actual finite-input flag guards and all H/I outcomes into the
**entire original function body** when both input infinity flags are zero.
`exec_zinv_finite_suffix` also exposes the body after the flag guards. Both
derive execution from the six caller fields, their square-input bounds and
writable private allocations only. Doubling uses the raw X/Y/Z; nonzero
arithmetic uses the actually weak-normalized U1/S1. Exact output coordinates,
flag, square-input bounds, all fourteen input/private allocation permissions,
and unchanged affine/inverse-Z field contents are returned. The frame is
explicitly outside the whole point block and private field blocks, and outside
affine bytes [0,80); it does not claim arbitrary-chunk point-padding framing.
The exact-source identity is closed; execution retains six inherited
assumptions. Normal compilation, recursive kernel checking and reviewed
no-update focused audits pass:

```sh
JET_TARGETS=C/jet_secp_zinv_finite.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_zinv_finite
```

`jet_secp_zinv_function.eval_zinv_function_finite` now derives the actual
finite-input function call: entry, **all thirteen** original local allocations,
the whole body, void return conversion and all thirteen frees. Initial caller
field contents/bounds, both finite flags and three distinct owned caller
allocations suffice; no local allocation, intermediate execution or desired
output is assumed. Exact coordinate words, output flag, unchanged affine and
inverse-Z fields, caller ownership, downstream bounds and external framing
survive the frees. The two locals unused on the finite path are still actually
allocated, kept owned and freed. Entry/metadata exports are closed; result
conversion retains four inherited logical assumptions and execution the same
six inherited assumptions. Normal build, recursive kernel checking and
reviewed no-update focused audits pass; reproduce with target/module
`C/jet_secp_zinv_function.vo` / `C.jet_secp_zinv_function` as above.
This is a finite-input C helper call, not all flags or a literal/public jet
equivalence. The fourth argument is an inverse-Z field pointer, not a NULL
ratio pointer.

`jet_secp_point_affine_product.eval_point_affine_product` now derives the
original multiplication from either affine X/Y into the matching point field.
It reuses the existing verified multiplier/log and undefined-point storage
lemma, retaining the true 128-byte destination ownership, both inputs,
product residue, square-input bounds and precise source/destination framing.
No initialized destination or multiplication call is assumed. Normal build,
recursive kernel checking and reviewed no-update focused audits pass with
target/module `C/jet_secp_point_affine_product.vo` /
`C.jet_secp_point_affine_product`; execution retains six inherited assumptions.

`jet_secp_zinv_infinite_products.exec_zinv_infinite_products` now derives all
four original A-infinity arithmetic statements: inverse-Z square/cube and
scaled affine X/Y. `jet_secp_zinv_infinite.exec_zinv_infinite_body` composes
them with the actual A flag guard, B-to-result flag copy, flag-dependent Z=0/1
assignment and early return. Every nonzero A flag and every B flag are covered;
the overwritten point coordinates need no initialized contents or bounds.
All five caller/private allocations, exact coordinate words, input fields,
output flag, machine bounds and external framing are retained. The proof
executes the actual statements, not a substituted `gej_set_ge` call.
Source identities and the bit-field bound are closed; execution retains six
inherited assumptions. Normal builds, recursive kernel checks and reviewed
no-update focused audits pass; reproduce with targets/modules
`C/jet_secp_zinv_infinite_products.vo` and `C/jet_secp_zinv_infinite.vo` / their
`C.*` module names as above.

`jet_secp_zinv_function_infinite.eval_zinv_function_infinite` now composes
A-infinity with the original function entry, all thirteen real local
allocations, the checked body, void return conversion and all thirteen frees.
Any nonzero A flag and any B flag are supported, without initial point-coordinate
contents or bounds. Exact result coordinates/flag, unchanged affine and
inverse-Z fields, all three caller ownership ranges, downstream bounds and
external framing are returned. All eleven unused private fields remain owned
through the body and are freed as well as the two used inverse temporaries.
Normal build, recursive kernel check and reviewed no-update focused audits
pass; execution retains six inherited assumptions. Reproduce with target/module
`C/jet_secp_zinv_function_infinite.vo` /
`C.jet_secp_zinv_function_infinite` as above.

`jet_secp_zinv_b_infinite.exec_zinv_b_infinite` now proves the remaining
A-finite/B-infinite body branch, reusing the actual 128-byte
`exec_gej_add_self_copy`. Its frame preserves all loads and permissions on old
valid blocks; no field initialization, affine range bound or optional-ratio
premise is needed. The source identity is closed and execution retains six
inherited assumptions. Normal build, recursive kernel check and reviewed
no-update focused audits pass with target/module
`C/jet_secp_zinv_b_infinite.vo` / `C.jet_secp_zinv_b_infinite`. Thus every flag
branch has a checked body proof. The B-infinity path is not yet a whole-call
theorem; the table caller instead has B.infinity=0 from the checked decoder.
Both A flag cases needed by that caller now have whole-call proofs.
`jet_secp_zinv_one_numeric` now proves the actual az/z12/U2/S2 word residues
and tight bounds at represented inverse-Z one, and derives both H/I residues
and square-input bounds. Raw X/Y may have limbs up to 2^60; no positioned or
canonical coordinate representation is imposed. All five exports are closed,
using the existing verified multiplication/square/weak-normalization models.
Normal build, recursive kernel check and reviewed no-update focused audits
pass with target/module `C/jet_secp_zinv_one_numeric.vo` /
`C.jet_secp_zinv_one_numeric` as above. This numeric bridge does not establish
the caller's inverse field or a literal/public jet result by itself.
`jet_secp_zinv_literal` now relates both actual loose-word H/I tests to the
literal Simplicity branch tests. `jet_secp_zinv_literal_outputs` proves the
entire normalized coordinate triple equals `literal_gej_ge_add`, for both
finite and infinite A, at represented inverse-Z one and arbitrary matching
square-bounded coordinates. No curve-membership or canonical-input premise
is added. Normal builds, recursive kernel checking and reviewed no-update
focused audits passed for both modules. These are arithmetic bridges, not
public jet execution proofs. The finite bridge uses only inherited functional
extensionality; the infinite bridge is closed.
`jet_secp_zinv_literal_call.eval_zinv_literal` now composes both complete
original C calls with their literal coordinate bridges. It derives entry,
all thirteen allocations/frees and return via the checked call proofs, and
returns the exact actual branch flag as well as its agreement with output
Z's literal zero test. The affine and inverse fields, ownership of all
three caller allocations, output limb bounds and external framing are
preserved. Its inverse-Z-one premise remains an internal caller obligation,
not a public input restriction. `jet_secp_zinv_flag` proves the reusable
finite flag/Z fact, closed, using the existing certified-prime theorem.
Normal build, recursive kernel checking and reviewed no-update focused
audits passed for `C/jet_secp_zinv_literal_call.vo` /
`C.jet_secp_zinv_literal_call`. Execution has the same six inherited
assumptions and no additional libc premise.
`jet_secp_double_loose_literal.eval_double_var_loose_literal` supplies the
other point operation of that loop: the complete original NULL-rzr doubling
call, with arbitrary matching square-bounded (not necessarily reader-canonical)
coordinates, both incoming infinity cases, exact literal output coordinates,
output flag/Z agreement, ownership, limb bounds and external framing. It
reuses the original execution and generic doubling-coordinate bridge.
Normal build, recursive kernel checking and reviewed no-update focused audits
passed for `C/jet_secp_double_loose_literal.vo` /
`C.jet_secp_double_loose_literal`. The pure flag lemma is closed; execution
retains the same six inherited assumptions and adds no libc model.
Next compose these calls and the table lookup in the descending generator
loop, then prove the public writer.
`jet_secp_generator_digit_add.exec_generator_digit_add` now derives the
original nonzero-digit lookup/addition statement pair for either table.
`generator_digit_add_source` identifies both pairs in the frozen Strauss
loop. The result is exactly the literal mixed-addition result for that
signed digit, with output flag/Z agreement, all three caller ownership
ranges, unchanged inverse field, output limb bounds, both readonly tables
and external framing. It derives the helper calls rather than assuming
their execution or result. Normal build, recursive kernel checking (including
all exhaustive table certificates) and reviewed no-update focused audits
passed for `C/jet_secp_generator_digit_add.vo` /
`C.jet_secp_generator_digit_add`. Execution retains the lookup proof's eight
inherited assumptions, adding no libc or table-correctness premise. The
short-circuit guards and full loop induction were separate obligations at
that checkpoint; they are now discharged by the following batch.

`jet_secp_generator_digit_control` proves both original short-circuit branches,
including exact array reads, assignment side effects, zero digits and omitted
high positions. `jet_secp_generator_loop_control` identifies the actual outer
loop, derives the empty non-generator loop for no=0, and proves its guard,
decrement, termination and composition rules. `jet_secp_generator_iteration`
then derives one complete original arithmetic body: double, empty inner loop,
and both optional signed generator additions. All its helper calls are derived.

`jet_secp_generator_loop.exec_generator_loop` proves the full original
descending loop for every count <=129, preserving both digit arrays through
external framing, both readonly tables, the inverse field, ownership, output
limb bounds and flag/Z agreement. Its internal input contract still requires
represented valid digits with the proved return-length zero prefix, no=0,
inverse-Z one and the initial point relation; these are caller obligations,
not new public-domain restrictions or a completed public generate proof.

`jet_secp_generator_program` ports the canonical generate step, step2..step128
and step129 routing from LibSecp256k1.hs:614--627, and proves its list-fold
interpretation and parametricity. `jet_secp_generator_loop_literal` identifies
the C loop result with that exact literal program given the digit-vector
relation, and proves removal of leading zero iterations from infinity,
including the all-zero case. All fourteen exports of these two pure modules
are closed. Execution keeps the lookup chain's eight inherited assumptions
and adds no libc or table-correctness premise. Normal builds, recursive kernel
checking and reviewed no-update focused audits passed for all six modules.
Reproduce the full dependency closure:

```sh
JET_TARGETS=C/jet_secp_generator_loop_literal.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_loop_literal
```

Next establish that loop contract from the actual caller and execute the
initializer/final correction/public writer; do not rebuild the loop induction.

`jet_secp_generator_digit_index` now derives the raw literal digit at each C
array index, its exact integer value/load, valid signed range and absence
above the actual returned length from the existing wNAF array theorem. It
also proves the high-to-low pair-vector relation needed by step129 and
transports the array invariant through framing. These are derived facts,
not new digit/correctness assumptions on a public jet.

`jet_secp_generator_final.exec_generator_final_one` derives the original final
flag read and conditional in-place Z multiplication, for any integer flag.
At represented denominator one its normalized Z is unchanged, with exact
X/Y and flag preservation, ownership, bounds and framing.
`jet_secp_generator_point_stage.exec_generator_point_stage` now composes the
**entire original point stage**: the real infinity initializer, actual loop
index initialization, descending loop and final correction. No initial
point contents, incoming point flag or intermediate execution is assumed.
The output is the canonical literal step129 applied to both actual literal
wNAF vectors. Its remaining internal caller premises include represented
wNAF producer results, actual length temporaries, no=0, the denominator-one
field, readonly tables and fresh caller allocations. The earlier scalar/
wNAF prefix, original external memset, function entry/frees and public writer
remain open; this is not a public generate theorem or added coverage.

All three modules passed normal compilation and reviewed no-update focused
assumption/contract checks. The full point-stage theorem has the same eight
inherited assumptions and no extra libc model. The initial independent recursive
kernel check for this **three-module extension** was
interrupted (exit 130) after more than 22 minutes of CPU-progressing execution
to prioritize independent public-jet acceptance. This is not a proof failure
or a successful kernel check; do not treat the earlier loop-only receipt as
checking these additional inputs.
The follow-up on immutable `1bb2a995` inputs terminated with exit 2 during
normal rebuilding, before kernel checking: `zinv_shared_preparation` timed
out on the closed `0 < 40` goal because `lia` processed the large unrelated
arithmetic context. The proof-only repair clears that context for closed
size facts and restricts block-separation search to `Sep`. Normal compilation
and existing no-update assumption/contract records pass without a timeout,
statement, assumption or target change. That repair alone did not complete the
full point check; entry/split/count-control checks below do not replace it.
The next rebuild on `aee7badb` exposed another context-heavy search in
`zinv_finite`'s `SepP` assertion (again exit 2 before kernel checking). Its
repair uses `NoDup_app_remove_r` for the actual list prefix, limits the other
separation assertion to `SepAll`, and isolates closed ownership sizes. Normal
compilation and unchanged no-update snapshots pass for this repair too.
The rebuild on immutable `47729b3f` inputs also terminated during normal
compilation, before kernel checking: the A-infinity function's thirteen-block
free-list proof exhausted its tactic timeout. Its precise residual goals are
negated disjunctions of block equalities. Explicit case analysis replaces
broad logical search, without changing the theorem or timeout. Normal
compilation and unchanged focused assumption/contract records pass for the
repair in `62ee7387`. The full point-stage rebuild, independent recursive
kernel check and focused no-update assumption/contract comparisons for
`generator_digit_index`, `generator_final` and `generator_point_stage` now
**pass on immutable `62ee7387`** in the dedicated verification worktree.
No type-in-type, unsafe fixpoint or assumed-positivity flags are reported.
This checks the complete point-stage dependency closure, not just its loop;
it still does not discharge the public caller's remaining premises.
Reproduce its check with:

```sh
JET_TARGETS=C/jet_secp_generator_point_stage.vo bash Coq/build-jets.sh -j1
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_point_stage
```
`C/jets-secp256k1.c:simplicity_generate` calls ecmult with the
constant infinity point and zero scalar, so the skipped non-generator loop
must establish that its initialized Z=1 persists; do not assume it.
For caller composition, retain the actual loose coordinate words and their
residues: `double_body_writer_outputs_literal` accepts arbitrary
square-bounded words with matching residues, and `mixed_x_matches_literal` /
`mixed_y_matches_literal` / `mixed_z_matches_literal` are generic in the H/I
and U/S fields. The new literal bridge reuses these instead of redoing them.
Do not specialize the loop state to canonical `square_reader_rho` words just
to apply the older reader-only mixed-addition endpoint.
These results do not establish all-input helper or public-jet equivalence;
accepted coverage remains 505/533 and the all-jet goal stays active.

## Decompression: current proof frontier

The complete original public C jet is proved by
`jet_secp_decompress_local.decompress_literal_local_spec`, against the
primitive-bearing `literal_decompress` composition. It is registered and
**passed ordinary scoped acceptance on `e32e7638`**: 416 kernel modules,
355 assumption records, 370 contract records, source and negative checks, all
five regenerated ASTs, and identical audit inputs before/after the run.
Normal compilation, recursive kernel checking and reviewed no-update focused
assumption/contract comparisons passed for this endpoint and its six new
public-wrapper modules. It retains the six inherited assumptions and adds no
libc model, curve-input restriction or intermediate-execution premise.

The public proof covers arbitrary valid 257-bit input/513-bit output cursors
and unrelated output contents. It derives the real by-value source-frame copy
and all three local allocations (src=16, x=40, r=88), reads parity and the field,
executes the original `ge_set_xo_var`, writes the result tag and either the
actual two-coordinate payload or two-field padding, returns true and frees all
locals. The failed-root outcome is an encoded `inl tt`, not a C jet failure.

The shared structure is reused rather than replaced:

- `jet_secp_decompress_reads` composes the original core bit reader and field
  reader and establishes `square_reader_rho`.
- `jet_secp_decompress_helper_literal` composes the actual copy, square,
  multiplication, +7, square-root chain, normalization, parity and conditional
  magnitude-one negation with their selected arithmetic/serialization bridges.
- `jet_secp_affine_write_prefix` generalizes the owned-field writer to an
  already-written prefix. `jet_secp_affine_skip` proves the actual two
  `skip_fe` calls; no substitute `skipBits(512)` call is used.
- `jet_secp_decompress_result_write` handles the tag, payload/padding,
  ownership and external framing.
- `jet_secp_decompress_public_{entry,prepare,body,rest,call}` discharges the
  public lifecycle and `jet_secp_decompress_local` exports the usual complete
  `secp_jet_local_spec`.

Reproduce the checked endpoint with Coq 8.17.1 and prepared dependencies:

```sh
JET_TARGETS='C/jet_secp_decompress_local.vo' bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_decompress_local
```

The existing `secp-field-integration/check-rescale.py` canonical-source and
whole-contract gate checks its catalog/type declarations, root input, parity
xor routing, exact literal composition and complete public theorem. It rejects
15 targeted mutations; the inventory's whole-contract regression checks pass.
Reproduce ordinary scoped acceptance on that commit, without update flags:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_decompress
```

The every-jet goal remains incomplete. Keep production C, original
specifications/domains/identities, API contracts and generation settings fixed.

## Projective addition: current proof frontier

The reusable caller interface is
`jet_secp_gej_add_generic_function.eval_gej_add_generic`. It derives the whole
original in-place helper call from bounded machine fields and proved residues,
rather than requiring those fields to have just come from a reader. Its result
includes the exact stored infinity bit, needed by `gej_equiv`. The generic finite
bridges and body proofs retain all control-flow, allocation and framing
obligations; they add no assumptions. `jet_secp_gej_pair_reads` separates the
six-word input width from the caller's required output space, including a
one-bit predicate result. These are shared proof interfaces, not additional
registered jets.

`simplicity_gej_add` is now **registered and scoped-accepted on `ba6b19e8`**. The target is
the original public `f_simplicity_gej_add`, with two unrestricted GEJ inputs
and the existing primitive-bearing `literal_gej_add` result. The internal modules
below passed ordinary compilation, recursive kernel checking and reviewed
no-update focused assumption/contract comparisons. Execution results retain
the six inherited assumptions and add no libc premise.

- `jet_secp_gej_add_statements` proves exact AST sharing with mixed addition:
  the difference operations, H/I guard and zero branch, H2/H3/T products and
  final X/Y tail. These seven source identities are closed.
- `jet_secp_gej_add_finite_start` executes the actual two finite dispatches
  and both Z squares, deriving the two squared fields, bounds, all four owners
  and precise external framing from storage. It reuses the selected coordinate
  square execution; the remaining preparation multiplications are not assumed.
- `jet_secp_gej_copy_owned` derives the actual 128-byte Clight struct copy,
  with all three field representations, infinity flag, ownership and framing.
- `jet_secp_gej_add_infinite` executes both early-return branches of the whole
  original helper body in place at A. B-infinity uses the existing sound
  self-copy proof, not a replacement skip. `jet_secp_gej_add_infinite_literal`
  connects both branches' serialized reader fields to `literal_gej_add`.
  The branch conditions are internal case splits, not a restricted public domain.
- `jet_secp_gej_fresh_product` reuses the actual affine-coordinate multiply
  proof for X/Y and restores the projective input's full 128-byte owner by
  precise framing. Its call adapter takes the real point/local identifiers.
- `jet_secp_gej_add_s_calls` proves both original S1/S2 two-call sequences
  through one identifier-parameterized proof. `jet_secp_gej_add_preparation`
  composes all six real preparation multiplications, preserving all six
  source coordinates, the two squared factors, eight owners and a frame that
  includes the infinity flags. It derives tight output bounds for the shared
  difference operations. Normal build, recursive kernel checking and reviewed
  no-update focused snapshots passed; no new assumption or libc premise is added.
- `jet_secp_gej_add_finite_prepare.exec_gej_add_finite_prepare` composes the
  actual two dispatches, both squares and all six multiplication calls. Its
  premises are the original six represented coordinates and owned allocations;
  both square factors and every intermediate execution are derived. It retains
  the six original coordinates, exact U1/U2/S1/S2 fields, both squares, tight
  bounds, eight owners and a frame including the infinity flags. Normal build,
  recursive kernel checking and reviewed no-update focused snapshots passed.
- `jet_secp_gej_add_finite_difference.exec_gej_add_finite_difference` extends
  that connected execution through the four actual H/I difference statements,
  reusing `exec_mixed_differences`. It derives both differences and their
  bounds from the original six coordinates, retaining those coordinates,
  U1/U2/S1/S2, both infinity flags, all ten owners and external framing.
  Ordinary compilation, recursive kernel checking and reviewed no-update
  focused assumption/contract comparisons passed. No intermediate execution
  or result is a premise.
- `jet_secp_mixed_zero_return.exec_mixed_zero_head_return` exposes the actual
  returning H guard for reuse; the existing `exec_mixed_zero_return` type and
  all its definitions are unchanged. `jet_secp_gej_add_finite_return` composes
  it with the connected prefix to execute the whole original projective helper
  body when H=0, covering both I-dependent doubling and infinity returns. It
  derives final coordinates, flags, bounds, all ten owners and framing from
  initial storage. H=0 is an internal case condition, not a public-domain
  restriction. Normal builds of this module and the existing mixed-addition
  and mixed-equivalence public endpoints, recursive kernel checks of their
  dependency closures and reviewed no-update focused snapshots passed.
- `jet_secp_gej_z_product` derives the actual fresh T=H*Bz call, with H first
  and the 128-byte point's Z second, reusing the selected multiplication log
  and arithmetic lemmas. `jet_secp_gej_add_nonzero_start` composes the actual
  nonzero guard, flag store, that fresh product, NULL ratio branch, Rz=Az*T
  multiplication and H square. It derives output fields, bounds, five owners
  and framing; T and H2 need no initialized contents. Normal compilation,
  recursive kernel checking and reviewed no-update focused snapshots passed.

The complete finite helper body is now connected:

- `jet_secp_gej_add_nonzero_tail` executes the entire actual H-nonzero tail,
  using the projective Z prefix above and the already-checked shared H2/H3/T
  and X/Y statements. It adds no intermediate-execution premise.
- `jet_secp_gej_add_finite_nonzero` composes that tail with the first 14
  statements, deriving the final fields, flag, bounds, all thirteen owners and
  framing from the six original coordinates and uninitialized private fields.
- `jet_secp_gej_add_finite_body.exec_gej_add_finite_body` combines the H=0 and
  H-nonzero cases, removing the H-case premise. It proves execution of the
  whole original helper body for both finite input flags, with exact machine
  output words, all eleven local owners, both point owners and framing.
  Ordinary compilation, recursive kernel checking of the full dependency
  closure and reviewed no-update focused assumption/contract comparisons
  passed for these three modules. The result retains the six inherited
  assumptions and no extra libc premise. It is not yet a public equivalence
  theorem: function/public lifecycles remain; the finite literal bridge is
  described below.

`jet_secp_gej_add_dispatch_literal` now connects the U1/U2/S1/S2 preparation
residues and H/I bounds to the literal finite-tree operands, for arbitrary
reader words. Its reader-test theorems prove that C's negated H and same-sign I
take the same zero branches as the specification. Normal compilation,
recursive kernel checking and reviewed no-update focused snapshots passed.
The machine residue/bound lemmas are closed; the literal bridges retain only
the inherited functional-extensionality assumption. Reproduce with
`JET_TARGETS='C/jet_secp_gej_add_dispatch_literal.vo' bash Coq/build-jets.sh -j2`
and `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_gej_add_dispatch_literal`.

`jet_secp_gej_add_finite_literal` connects all three actual finite output-word
functions to the fixed `literal_gej_add` result, including doubling/infinity
branches and the extra Bz factor in the nonzero Z path. It reuses the existing
X/Y and doubling writer bridges. `jet_secp_gej_add_finite_body_literal` composes
that result with execution of the whole original finite C body, deriving the
serialized specification result, bounds, all thirteen owners and framing from
reader storage. The finite flags are internal dispatch cases; no curve or
canonical-word restriction is imposed. Both modules passed normal compilation,
recursive kernel checking and reviewed no-update focused snapshots. The value
bridge retains only inherited functional extensionality, and the execution
bridge retains the six inherited assumptions with no extra libc premise.
Reproduce with `JET_TARGETS='C/jet_secp_gej_add_finite_body_literal.vo'
bash Coq/build-jets.sh -j2` and `bash Coq/build-jets.sh --coqchk
-bytecode-compiler yes -silent -o C.jet_secp_gej_add_finite_body_literal`.

Reproduce this checked internal frontier:

```sh
JET_TARGETS='C/jet_secp_gej_add_infinite_literal.vo C/jet_secp_gej_fresh_product.vo' bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_add_infinite_literal C.jet_secp_gej_fresh_product
```

The preparation block computes U1=Ax*Bz^2, U2=Bx*Az^2,
S1=(Ay*Bz^2)*Bz, S2=(By*Az^2)*Az, reusing
`eval_field_point_mul_numeric PointZ` for the two in-place products. Reproduce:

```sh
JET_TARGETS='C/jet_secp_gej_add_preparation.vo' bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_add_preparation
```

Reproduce the connected prefix with `JET_TARGETS='C/jet_secp_gej_add_finite_prepare.vo'
bash Coq/build-jets.sh -j2`, then `bash Coq/build-jets.sh --coqchk
-bytecode-compiler yes -silent -o C.jet_secp_gej_add_finite_prepare`.

Reproduce the H/I frontier with
`JET_TARGETS='C/jet_secp_gej_add_finite_difference.vo' bash Coq/build-jets.sh -j2`,
then `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_gej_add_finite_difference`.

Reproduce that whole-body zero case with
`JET_TARGETS='C/jet_secp_gej_add_finite_return.vo C/jet_secp_mixed_local.vo C/jet_secp_gej_ge_equiv_local.vo'
bash Coq/build-jets.sh -j2`, then `bash Coq/build-jets.sh --coqchk
-bytecode-compiler yes -silent -o C.jet_secp_gej_add_finite_return
C.jet_secp_mixed_local C.jet_secp_gej_ge_equiv_local`.

Reproduce the nonzero Z prefix with
`JET_TARGETS='C/jet_secp_gej_add_nonzero_start.vo' bash Coq/build-jets.sh -j2`,
then `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_gej_add_nonzero_start`.

Reproduce the unified finite body with
`JET_TARGETS='C/jet_secp_gej_add_finite_body.vo' bash Coq/build-jets.sh -j2`,
then `bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_gej_add_finite_body`.

`jet_secp_gej_add_body_literal` composes the infinity and finite branches
without excluding any reader inputs, and derives actual void-result conversion.
`jet_secp_gej_add_function_entry` proves the exact eleven-local entry and free
list (closed). `jet_secp_gej_add_function.eval_gej_add_literal` derives the whole
original `gej_add_var` call from reader storage: all eleven allocations, the
body, result conversion and eleven frees. It returns represented, bounded
coordinates matching `literal_gej_add`, both point owners and external framing.
These three modules passed normal compilation, recursive kernel checking and
reviewed no-update focused snapshots; the execution proofs retain the six
inherited assumptions and no extra libc premise. Reproduce with
`JET_TARGETS='C/jet_secp_gej_add_function.vo' bash Coq/build-jets.sh -j2` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o
C.jet_secp_gej_add_function`.

`jet_secp_gej_add_local.gej_add_literal_local_spec` proves the complete public
jet. Its seven public modules derive both original GEJ reads, the helper call,
the original writer and true return, the actual source-frame copy and all three
public allocations/frees (16/128/128 bytes). Inputs span 1536 bits, outputs 768;
valid cursors and unrelated output contents are arbitrary. No curve or
canonical-input restriction and no libc premise is added. Normal compilation
and reviewed no-update focused snapshots passed. The existing canonical-source
gate now checks the GejAdd catalog route, shared literal tree and complete
public type, rejecting ten targeted mutations; inventory regressions pass.

The full scoped check passed on the exact registration commit `ba6b19e8`,
without update flags:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_add
```

It checked 450 kernel modules, 389 assumption records, 404 contract records,
negative tests and all five regenerated ASTs, on unchanged audit inputs.
The every-jet goal remains incomplete.

## Projective equivalence: scoped-accepted on `0cb928b9`

`jet_secp_gej_equiv_local.gej_equiv_literal_local_spec` covers the complete
original public C jet against the exact fixed `gej_negate`/`gej_add`/
`gej_is_infinity` composition. It accepts all six Word256 coordinates and
general valid frame cursors and output contents; no curve, canonical-coordinate
or enlarged-output-space restriction is imposed. The generic addition contract
handles the actual non-reader limbs produced by negation and proves the stored
infinity flag, rather than inferring that flag from an unproved representation
invariant. Both GEJ reads use the output-width-parameterized shared reader proof.
Normal build, recursive kernel checking and reviewed no-update focused
snapshots passed. Execution inherits the six existing assumptions and adds no
libc premise. Its canonical-source gate checks catalog dispatch, representation,
literal composition and the whole public contract, rejecting 13 mutations.
Reproduce scoped acceptance on its registration commit with:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_equiv
```

On `0cb928b9`, the command passed on unchanged inputs: 472 kernel modules,
411 assumption records, 426 contract records, negative tests and all five
regenerated ASTs. The every-jet goal remains incomplete.

## Extended mixed-addition ratio: formal obstruction

`jet_secp_mixed_ex_counterexample.gej_ge_add_ex_public_counterexample`
constructs the full original public Clight execution on fresh disjoint frames
over initialized program memory for A=((0,p),1), B=(0,0), and proves its output
memory contradicts the fixed literal specification. C returns ratio zero;
the specification returns the noncanonical word p. All public calls, local
allocations/frees and witness conditions are discharged. Normal compilation,
recursive kernel checking and reviewed assumption/contract checks passed.
No target or input-domain correction is made; this jet remains unresolved
and coverage stays 505/533. See [JET_SECP_RATIO_MISMATCHES.md](JET_SECP_RATIO_MISMATCHES.md)
for the exact theorem, reproduction commands, historical native evidence and
verification limits. The investigation claim is released; do not register a
restricted or corrected-target equivalence as if it resolved this mismatch.

The separate `jet_secp_mixed_ex_refutation.gej_ge_add_ex_not_literal_local_spec`
also refutes the exact existential local-spec contract by reusing the existing
Clight uniqueness theorem. It additionally inherits CompCert's two standard
external-call property axioms; the original counterexample retains its six
assumptions. Neither statement permits changing the targets or counting this
jet as accepted. See the mismatch report for the precise distinction.
The refutation's dependency closure was rebuilt and recursively kernel-checked
again on `fa45127e` in the main checkout; its existing focused assumption and
contract records also match without updates. This confirms the reported
obstruction, not any additional equivalence coverage.

## Field inversion: checked preparation, public proof still missing

The actual `fe_inv_var` uses signed62 conversion and `modinv64_var`, not the
square-root addition chain. Seven ordinary modules now establish the actual
conversion calls, exact numeric values and limb ranges, their round trip,
40-byte Clight struct copying, the production modulus global and its initial
memory, and the exact inversion entry/body composition. In particular,
`jet_secp_modinfo_fe_copy` executes the first modular-inverse copy from the
readonly sparse modulus; it does not require that source to be writable or
canonically represented. The numeric bridge lemmas are closed. Execution
inherits the existing assumptions and introduces no external-library model.
Normal compilation, recursive kernel checking and reviewed no-update
assumption/contract snapshots passed for the seven-module dependency chain.
Reproduce the focused build and kernel check with:

```sh
JET_TARGETS="C/jet_secp_signed62_storage.vo C/jet_secp_modinfo_fe_copy.vo C/jet_secp_fe_inv_statements.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_signed62_storage C.jet_secp_modinfo_fe_copy C.jet_secp_fe_inv_statements
```

These are preparation results, not an inversion jet proof: the structural body
composition still takes the modular-inverse call as an internal premise.
Remaining obligations include actual production divstep batches and lifting
arithmetic termination to their execution, signed128 updates, length shrinking,
sparse-modulus normalization, the canonical word-level Bezout bridge, and the
complete public caller with allocation/freeing and frame preservation. No
inversion registration or coverage increase is claimed.

`jet_secp_divstep_termination.inv_divstep_terminates` now proves that the
existing integer divstep transition reaches `g = 0` for every state (whose
record requires odd `f`), and `inv_divstep_batches_terminate` lifts this to
62-step boundaries using zero stability. All sixteen exported lemmas are
closed; normal compilation, recursive kernel checking and reviewed no-update
snapshots passed. Reproduce with
`JET_TARGETS=C/jet_secp_divstep_termination.vo bash Coq/build-jets.sh -j2` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_divstep_termination`.
The normal build reuses unmodified `extraMath.v`, `modinv.v` and `divstep.v`,
with only `divsteps_def.v` from the existing pinned safegcd source. The
definitions-only shell and Nix dependency builds passed; neither compiles the
724-step certificate. This removes the arithmetic termination obligation, not
the pending production-loop execution, machine-bound or specification bridge
obligations.

`jet_secp_divstep_bounds.inv_256_batch_eta_safe` additionally proves
`-320 <= eta < 320` throughout any 62-step batch started by a 256-bit
trajectory: the initial batch may have zero input, and subsequent batches
require precisely the nonzero-`g` continuation test. The bound includes the
trailing steps of a batch after `g` reaches zero. It follows from a preserved
`delta + log2(abs(g))` bound, not a fixed iteration certificate. All seven
exported lemmas are closed; normal compilation, recursive kernel checking and
reviewed no-update snapshots passed. Reproduce using the same focused commands
above with `jet_secp_divstep_bounds` in place of `jet_secp_divstep_termination`.
This supplies the arithmetic `eta` bound for a future execution invariant; it
does not establish that the C batch implements the transition, or prove its
other machine-operation and storage obligations.

There is also a fixed-program external-call boundary, independently of the
remaining arithmetic. The production `ctz64_var` selects `__builtin_ctzl`,
whose pinned CompCert lookup returns `None` and hence uses abstract external
semantics. The diagnostic module `jet_secp_ctz_semantics_gap` checks that
dispatch and proves that generic external-call properties alone do not imply
even a return for valid argument 1. It adds no ctz premise or jet coverage.
The checked `jet_secp_ctz_external_call` now establishes this boundary through
the actual helper execution: any completed `ctz64_var` call entails an
external call on the same argument and initial memory; a supplied integer
external result with empty trace suffices to execute the complete helper.
This is an explicit unresolved dependency, not a counting model or public
inversion theorem. The necessity result has not yet been lifted through a
divstep batch or public jet. Neither direction adds coverage.
See [JET_SECP_EXTERNAL_MISMATCHES.md](JET_SECP_EXTERNAL_MISMATCHES.md) for the
precise formal evidence, the related wNAF `memset` boundary, and the distinction
between this model gap and a demonstrated native C/specification bug. Do not
switch to a different generated fallback or count a new external-model
assumption as a discharged public equivalence proof.

The older VST development under `C/secp256k1/` supplies reusable pure arithmetic,
but its VERIFY translation unit is not the production program. Its canonical
modinfo representation also differs from the actual field constant's negative
low limb and sparse high limb. Reuse proved arithmetic with explicit adapters;
do not assume that its execution theorem applies unchanged or replace the
fixed Bezout specification with exponentiation.

[JET_INHERITED_REVIEW.md](JET_INHERITED_REVIEW.md),
[JET_FIDELITY_REVIEW.md](JET_FIDELITY_REVIEW.md) and the `JET_*_MISMATCHES.md`
reports describe these boundaries. Production C, canonical Haskell and the
frozen `Coq/Simplicity` model must not be changed to make a proof pass.

Unique earlier candidates, diagnostic witnesses, derived trees and the parallel
field multiplication/square alternative remain in `../../proof-work/`, outside
the active build. See its README for recovery instructions and archive limits.
Their presence does not register or accept additional jets. Current acceptance
is reproduced with `bash Coq/check-jets.sh --accept`; old run records and
continuation journals are not required.

## Generation: checked scalar-splitting dependency, public proof missing

`jet_secp_scalar_split128.eval_scalar_split128_owned` executes the actual
`secp256k1_scalar_split_128` into two uninitialized, separate scalar objects.
It exposes the exact four machine-word loads of each output, the low/high
128-bit values and bounds, ownership of both destinations and an owned input,
and framing. A shared boolean interface also permits a read-only input
without assuming it writable or Freeable. The arithmetic covers every
four-word input; normalization remains a separate caller obligation.

Normal compilation, recursive kernel checking and reviewed no-update
assumption/contract snapshots passed. The numeric decomposition is closed;
execution inherits the six existing assumptions, with no libc-model premise.
Reproduce with:

```sh
JET_TARGETS=C/jet_secp_scalar_split128.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_scalar_split128
```

This closes a concrete generator/ecmult preparation call, not `generate` or
another public jet. Remaining obligations include the actual wNAF execution
and digit/specification bridge, precomputed-table contents and their startup
and preservation, the point-operation loop, literal program correspondence
and public reader/writer/allocation lifecycle. The original wNAF also calls
external `memset`; that library boundary is reported in
[JET_SECP_EXTERNAL_MISMATCHES.md](JET_SECP_EXTERNAL_MISMATCHES.md), not assumed
discharged by the splitting proof. Coverage remains 505/533.

`jet_secp_scalar_split128_literal` now ports the exact canonical normalized
`scalar_split_128` routing (low half first, both sign bits false), and relates
the original C split's output memory to its two literal Word128 payloads.
`eval_scalar_split128_normalized_literal` derives the original complete helper
call, exact `scalar_at` words suitable for the existing wNAF contract, both
destination ownership ranges, the owned-input option, and framing. The input
normalization/value equality is an internal caller obligation, not a new
restriction on public inputs: `scalar_reader_split128_value` proves it for
the actual reader limbs for every Word256 input. The three-region relation
from reader storage is now derived in the following module; composing the
actual caller statements and both wNAF calls remains open. Do not treat the
arithmetic bridge alone as that caller composition.
Normal compilation and reviewed focused snapshots pass; six exports are
closed, storage uses four inherited assumptions, and complete C execution
uses the existing six without a libc premise. Independent recursive kernel
checking and no-update focused audits pass on `c7bcfcd2`. Use the normal target/module
`C/jet_secp_scalar_split128_literal.vo` / `C.jet_secp_scalar_split128_literal`
with the commands above. The unchanged scalar-parametric dependency was
rebuilt from source under pinned Coq 8.17.1 / OCaml 4.14.4; its existing
assumption/contract snapshots match without updates. No jet is registered by
this bridge; current accepted coverage remains 513/533.

`jet_secp_scalar_split128_storage` removes the symbolic memory relation from
that call boundary. It derives it from two distinct fresh owned32 destinations
and readable, aligned source scalar storage, at any valid source offset.
`scalar_split128_rep_after_reader` instantiates it with the actual reader's
final storage for every Word256 input. The complete original split call then
returns both exact literal Word128 scalar arrays, both destination ownership
ranges and framing outside the three regions. The source need not be writable
or Freeable, and destination initial contents are arbitrary. The three memory
adapters use four inherited assumptions; complete execution uses six, with no
libc model. Normal compilation and reviewed no-update focused audits pass.
Independent recursive checking and no-update focused audits pass for the
committed `809ebb5a` extension in the task-owned verification worktree; this
also checks the scalar-parser proof optimization's existing snapshots.
Reproduce with target/module
`C/jet_secp_scalar_split128_storage.vo` / `C.jet_secp_scalar_split128_storage`.

Clean rebuilding exposed two proof-computation bottlenecks. The u128 layout
proof now projects only struct/member metadata instead of materializing the
generated dependent consistency certificate (`c7bcfcd2`); the scalar byte
parser proof uses an explicit equality intermediate instead of folding its
expanded symbolic expression (`e2259b24`). Statements and assumption/contract
snapshots are unchanged and no-update checks pass. Neither optimization
changes the compiler baseline, production AST, generation settings or target.
The existing coverage regression suite also passes; neither adapter adds
public coverage. Next compose the real caller's setup/non-generator skip,
split and wNAF stages; the external memset boundary remains separate.

`jet_secp_generator_zero_scalar.eval_generator_scalar_zero` derives the
original scalar-zero helper call for the generator's four-zero readonly
scalar, at any valid aligned source offset, with exactly unchanged memory
and an empty trace. It requires neither writable nor Freeable source storage.
The memory-identity lemma is proved by inverting the original function's
entry, actual temp-only body and release, not by assuming a no-write effect.
Normal compilation and reviewed no-update focused snapshots pass. Four
computed support exports are closed, the representation lemma has four
inherited assumptions, and execution/memory identity has six. Independent
recursive checking and no-update focused audits pass on `80a813b8`. This
discharges the readonly zero-scalar call needed to skip Strauss preprocessing;
it does not register another jet or establish the whole caller.

`jet_secp_generator_preprocess.exec_generator_preprocess_zero` now derives
the entire original first Strauss preprocessing loop for the fixed one-point,
zero-scalar call made by `generate`: index initialization, bounds guard,
original scalar-zero call, short-circuit `continue`, increment and terminating
guard. It assumes no execution/result and does not inspect the unused point.
Memory is exactly unchanged; every temporary except np/t'1/t'2 is preserved,
so the initialized no=0 and denominator-one memory survive. The logical jet
input scalar is not restricted by this fixed auxiliary zero scalar.
Normal compilation and reviewed no-update focused snapshots pass; the five
source/lookup exports are closed and execution retains six inherited
assumptions, with no libc model. Independent recursive checking and no-update
focused audits pass for this module and the readonly zero-scalar helper on
`80a813b8`. Remaining
before generator splitting: original zero-length ge_table_set_globalz call,
the skipped auxiliary loop, and the caller setup/allocations.

`jet_secp_generator_globalz_empty.eval_ge_table_set_globalz_empty` now derives
the original zero-length helper call, including both real local allocations,
the unsigned index underflow, false length guard, void result and both frees.
It needs no readable/writable argument-array premise because the original
zero-length branch never dereferences them. `Mem.unchanged_on True` preserves
all old contents and permissions in both directions (new private blocks may
have been allocated and freed). Normal compilation and reviewed no-update
focused audits pass; source/block metadata is closed, and execution retains
six inherited assumptions without a libc premise. Independent recursive
checking and no-update focused audits pass on `a43f28e4`; the real caller's
state-field loads and linkage are composed in the following module.

`jet_secp_generator_globalz_call.exec_generator_no_points` now composes the
three original statements before generator splitting: preprocessing, state
pre_a/aux pointer loads and the actual global-Z helper call, then the skipped
auxiliary multiplication loop. The field layout and shift/multiply count
expression are derived from the frozen AST. The resulting phase retains
no=0 and all unrelated temporaries and satisfies `Mem.unchanged_on True`,
including old readonly table permissions. Its internal input contract still
requires num=1, the fixed auxiliary zero scalar, initialized state pointers
and no=0; actual counter/Z initialization and caller allocation/setup remain
to compose. It adds no public-input scalar restriction, no helper execution
or result premise, and no libc model. Normal compilation and reviewed
no-update focused snapshots pass; five source/lookup exports are closed,
two expression exports use four inherited assumptions, and all three
execution exports use six. Recursive kernel checking and no-update focused
audits pass for this phase and the zero-length helper on `a43f28e4` in the
task-owned verification worktree. No coverage row is added.

`jet_secp_generator_initialize.exec_generator_prepare_non_generator` now
derives the **entire original first eight statements**: actual counter/no
initialization, original fe_set_int(1) on the real 40-byte Z object, and the
three-statement no-points phase. It does not assume initialized counters,
initial Z contents or represented denominator one. It derives the zero-scalar
storage and state-pointer loads after the setter using its checked separation
frame. The result retains the exact denominator-one words, its Freeable40
ownership, exact temporary updates and framing outside Z. The initial local
environment, fresh Z object, fixed readable zero scalar, num=1 and state
pointer fields are still entry/setup obligations, not new public input
restrictions. Normal compilation and reviewed no-update focused snapshots
pass. Four source/lookup exports are closed and three execution exports retain
the existing six assumptions, with no libc model. Independent recursive
kernel checking and no-update focused audits pass on `1b96a00e` in the
task-owned verification worktree. Reproduce with the normal
target/module `C/jet_secp_generator_initialize.vo` /
`C.jet_secp_generator_initialize`, as for the other generator modules above.

The unchanged fe_set_owned and scalar-read framing dependencies were rebuilt
from source under pinned Coq 8.17.1 / OCaml 4.14.4 after their old objects
reported inconsistent assumptions over the proof-only u128-layout refactor.
No source, theorem or target was changed to accept those old objects. Next
derive caller entry/setup (including the actual readonly zero-scalar global),
compose this prefix with scalar splitting and both original wNAF calls, then
reuse the existing point-stage proof and public writer. The original external
memset boundary remains explicitly unresolved. Coverage is still 513/533.

`jet_secp_generator_zero_global` derives the real readonly `_na` global's
four zero words and exact 32-byte permission bounds from
`Genv.init_mem jets_secp.prog`; existence reuses the checked original program
initialization. Its symbol is resolved by identifier, not a numeric block.
It proves preservation across allocations and unchanged regions, separation
from Freeable storage, the original global-address expression and the actual
scalar-zero helper call. This closes the fixed auxiliary scalar's initial
storage obligation, not the arbitrary logical input or the full public jet.
Normal compilation and reviewed no-update assumption/contract checks pass;
the two symbol/info facts are closed, memory/address results use four inherited
assumptions, and helper execution uses the existing six without a libc model.
Independent recursive kernel checking and no-update focused audits pass on
`2b7104e2` in the task-owned verification worktree. Reproduce
with target/module `C/jet_secp_generator_zero_global.vo` /
`C.jet_secp_generator_zero_global` using the commands above.

`jet_secp_ecmult_state.exec_ecmult_state_initialize` derives all three
original `ecmult` state-pointer assignments and their actual Mptr loads from
arbitrary prior state contents. It preserves Freeable24 ownership and memory
outside the state object. `jet_secp_ecmult_entry.ecmult_entry_and_state`
derives the real function entry, four original allocations (320/704/1040/24
bytes), those assignments, pairwise and old-memory separation, all four
ownership ranges and `Mem.unchanged_on True` for the caller's old memory.
No local allocation, initialized pointer or helper execution is assumed by
this combined theorem. Source/layout/allocation facts are closed; the three
C execution facts use the same six inherited assumptions without a libc
model. Normal compilation and reviewed no-update focused audits pass.
Independent recursive kernel checking and no-update focused audits pass on
`5d036c28` in the task-owned verification worktree. Reproduce with target/module
`C/jet_secp_ecmult_entry.vo` / `C.jet_secp_ecmult_entry`; focused audits select
both `C.jet_secp_ecmult_state` and `C.jet_secp_ecmult_entry`.

`jet_secp_generator_entry.generator_entry_and_prepare` now derives the actual
Strauss function entry, all nine original local allocations and the checked
first-eight-statement prefix. It takes only the fixed readonly auxiliary
scalar state and the caller's two pointer loads (established by the actual
ecmult setup above), with arbitrary result/point/generator argument values.
It derives denominator one, exact ready temporaries, pairwise and old-memory
separation, all nine Freeable ownership ranges and framing outside the new Z
object. Initial counters, local contents, local allocation/ownership and
intermediate executions are not premises. The proof reuses the existing
allocation/framing tactic structure from mixed-addition lifecycle proofs.
The two entry/layout facts are closed; the complete entry/prefix result uses
the same six inherited assumptions, without a libc model. Normal compilation
and reviewed no-update focused audits pass. Independent recursive kernel
checking and no-update focused audits pass on `7fa7fb44` in the task-owned
verification worktree. The existing coverage regression suite also passes;
helpers are not counted as complete jet equivalences. Reproduce with target/module
`C/jet_secp_generator_entry.vo` / `C.jet_secp_generator_entry`.

Next compose the scalar-split and wNAF stages with this actual entry/prefix,
then reuse the existing point-stage proof and public writer/cleanup. The
actual external memset boundary remains separate; these entry/setup proofs
do not register `generate` or increase the accepted count.

`jet_secp_generator_split_call.exec_generator_scalar_split` now derives the
actual original call inside the nonnull-ng branch, from the caller's local
bindings, owned destinations and represented normalized scalar. It reuses
the checked C split/literal bridge and returns both exact literal 128-bit
words, destination ownership and framing outside the three scalar blocks.
Its source equations retain the following original wNAF setup as a separate,
unexecuted suffix. `jet_secp_scalar_split128_effects.scalar_split128_permissions`
derives unchanged nextblock and all permissions by inverting the original
function entry, eight-store body and empty release. It assumes no effect law;
the call theorem derives the call and applies this effect result, preserving
the source scalar's permissions for later cleanup. Three source/foot facts
are closed; the effect and C execution results use the existing six inherited
assumptions without a libc premise. Normal compilation and reviewed no-update
focused audits pass. Independent recursive kernel checking and no-update
focused audits pass on `83f174c0` in the task-owned verification worktree. Reproduce
with target/module `C/jet_secp_generator_split_call.vo` /
`C.jet_secp_generator_split_call`, selecting it and
`C.jet_secp_scalar_split128_effects` for focused audits. This is not the
whole guarded branch or public `generate`, and adds no coverage row.

`jet_secp_generator_entry_split.generator_entry_and_scalar_split` now composes
the actual entry/preparation with that original split call. Its initial
conditions are the readonly fixed zero scalar, the caller's two state-pointer
loads and the normalized scalar storage already produced by the original
reader. It derives all nine local allocations, separation and ownership,
preservation of input storage through preparation, and the real ng guard's
truth from a weak-valid-pointer proof (not merely the Vptr constructor).
It returns both literal halves, denominator one, all local ownership, the
source scalar's old permissions and framing of other old memory. There is
no intermediate execution or result premise. The complete theorem has the
same six inherited assumptions and no libc model. Normal compilation and
reviewed no-update focused audits pass. Independent recursive kernel checking
and no-update focused audits pass on `a50ef23d` in the task-owned verification
worktree. Reproduce with target/module
`C/jet_secp_generator_entry_split.vo` / `C.jet_secp_generator_entry_split`.
This is explicitly entry, preparation, guard and split, not the following
two wNAF calls or the complete guarded branch. Their memset boundary remains
unresolved; public coverage stays 513/533.

`jet_secp_generator_bits_max.exec_generator_bits_max` now derives the two
original count-maximum updates after the wNAF calls. For actual returned
counts in `[0,129]` and initial bits=0, it executes both signed comparisons
and conditional assignments, derives bits=`Z.max low high`, preserves every
other temporary, and leaves memory exactly unchanged. The bounds are the
existing internal wNAF return bounds, not a restriction on public scalar
inputs. Its generic one-update lemma is shared by the two concrete fields.
Three source/map facts are closed, the comparison uses four inherited
assumptions, and both execution results use six without a libc premise.
Normal compilation and reviewed no-update focused audits pass. Independent
recursive kernel checking and no-update focused audits pass on `1bb2a995`
in the task-owned verification worktree. Reproduce with target/module
`C/jet_secp_generator_bits_max.vo` / `C.jet_secp_generator_bits_max`.
This closes the final count-control segment needed by the existing point
stage, not the preceding two actual wNAF calls or their memset boundary.

`jet_secp_wnaf_entry15.wnaf_entry15_owned_output` now derives the original
wNAF function entry, its fresh 32-byte scalar local, four actual temporary
initializations and all four original disabled-assertion loops for the
generator's actual len=129/window=15 calls. It establishes the existing loop
fields without assuming initialized private data or execution. The actual
memset arguments evaluate to `(destination, 0, 516)`; the owned destination
retains all 516 Freeable bytes and is distinct from the fresh scalar. All
old memory and permissions are unchanged up to that call. Six source/entry/
map facts are closed, argument evaluation uses four inherited assumptions,
and the three C execution results retain six without an extra libc premise.
Normal compilation, recursive kernel checking and reviewed no-update focused
audits pass on `fa45127e` for this new module's closure in the main checkout.
Reproduce with target/module
`C/jet_secp_wnaf_entry15.vo` / `C.jet_secp_wnaf_entry15`.
This stops before memset: it neither assumes zeroed digits nor claims that
the abstract external call exists, returns successfully or has a zeroing
effect. It adds no public coverage; the existing post-memset literal proof
still needs this external boundary discharged and the original release
composed before it yields a complete wNAF call.

`jet_secp_scalar_get_bits.eval_scalar_get_bits_slice` now derives the whole
original single-word bit-reader call from concrete `scalar_at` storage for
any 256-bit value. For offsets in `[0,256)`, counts in `[0,32]`, and a window
contained in one 64-bit limb, it returns the represented value
`(value / 2^offset) mod 2^count`, with the exact same memory and an empty
trace. This covers wNAF's top-bit read at `(255,1)` and its one-bit loop reads.
The proof includes the actual no-op assertion loop, field/index load, shift
guards, mask, return cast and function lifecycle. It reuses the checked
repacking mask and unsigned-shift lemmas, adds no external model, and does
not require a canonical scalar or writable storage.

This is a helper, not public coverage. Reproduce this helper with
the two commands above, replacing `jet_secp_scalar_split128` with
`jet_secp_scalar_get_bits`.

`jet_secp_scalar_bits_var.eval_scalar_get_bits_var_slice` now also derives the
complete original cross-word reader, for any 256-bit value, offsets in
`[0,256)`, counts in `[1,32)`, and `offset + count <= 256`. The result is again
`(value / 2^offset) mod 2^count`, with the exact original memory and empty trace.
The same-word branch calls the original reader through checked linkage; the
cross-word branch loads both actual limbs and combines their shifted parts.
The proof derives the branch condition, nonzero shift/complement bounds, and
second-limb bounds, rather than assuming a favorable branch or read result.
It reuses the existing mask, shift, radix-slice and single-word execution
lemmas, with no external model or canonical-scalar premise. Reproduce it with
the same commands, replacing the module name with `jet_secp_scalar_bits_var`.

These are internal reader contracts. Proving that the actual wNAF caller
maintains their count/offset/storage premises, then executing its carry/digit
loop and relating that loop to the literal point program, remain public-proof
obligations. The external `memset` boundary and the other generation obligations
above remain unresolved. Neither reader increases coverage.

`jet_secp_wnaf_digit.exec_wnaf_window_digit` now composes the original window
reader call with the actual word addition, signed carry extraction, digit
subtraction and output-array store. It covers `2 <= w <= 31`, positive window
width at most `w`, and a window ending within the 256-bit scalar. Its carry is
0 or 1, the stored digit has the original sign multiplier, and the digit
before that multiplier is odd and strictly between `-2^(w-1)` and `2^(w-1)`.

The weighted-value equation is derived together with the concrete execution
and store. In particular, a shorter final window has no spurious carry at
the full window width. The low-bit/carry mismatch premise is the nonzero
branch's condition, not a restriction on scalar inputs. The predecessor still
has to establish that condition through its actual read and branch. The
output store is constructed from writable-cell access, not assumed; scalar
bytes and the reader's result are supplied by the existing storage model and
checked call theorem. Source identities tie the selected statements to the
original wNAF loop, and the sequence-association proof preserves its actual
call/add grouping. No external-library model is added.

Reproduce this internal reader-to-store phase with the same build/kernel
commands above, using `jet_secp_wnaf_digit`.

`jet_secp_wnaf_control.exec_wnaf_loop_body_step` composes that phase with the
original low-bit read and branch, actual window clamp, skipped-bit `continue`,
and last-set-bit/counter assignments. It executes one complete original loop
body, for either branch, and constructs the resulting memory and temporaries.
The bit index strictly increases without exceeding `len`; the carry remains
0 or 1, the last-set-bit bound is preserved, and the weighted residual equation
holds. A skipped bit leaves memory unchanged. A nonzero step performs exactly
the signed-digit store exposed by the phase theorem. Distinct output/scalar
blocks preserve concrete scalar storage through that store. Writable access
and the output address bound are premises for the current cell, not an assumed
execution or store result. The caller still has to supply them for every
iteration. No external-library model is added.

Reproduce the body step with the same build/kernel commands, using
`jet_secp_wnaf_control`.

`jet_secp_wnaf_loop.exec_wnaf_loop` now derives execution and termination of
the complete original loop from a concrete array invariant. Its induction uses
the decreasing number of remaining bit positions; it does not assume a loop
execution or a fixed number of successful stores. The invariant connects each
logical digit to its actual signed `Mint32` load, keeps unvisited cells zero,
preserves writable access for subsequent iterations, and identifies the highest
nonzero digit. All digits are zero or odd in the strict window bounds. The
weighted digit sum and residual value are preserved together with scalar
storage, all memory permissions, the allocation frontier, and loads outside the
output block.

`exec_wnaf_loop_zero` specializes this to initially zero cells and the original
bit/carry/last-set-bit state, then executes the original return statement. It
returns the last nonzero index plus one in `[0,len]`, with exact output-array
loads. The general equation retains the final residual and carry explicitly.
The strengthened conclusion proves that under `n < 2^(len-1)`, the final carry
is zero and the weighted digit sum is exactly `n`. The finishing-step proof
covers both the skipped-bit and nonzero branches, including shortened final
windows, and is propagated through the actual loop induction. This adds a
conditional conclusion, not a new premise or input restriction on the general
execution theorems. For the `len = 129` calls after scalar splitting, the bound
is precisely the existing `n < 2^128` result of `eval_scalar_split128_owned`;
composing that caller and its storage representations is still pending.
Zero loads and the initial scalar/frame state must still be derived from the
actual function prefix, including its external `memset`. This theorem therefore
does not add a libc model or discharge that boundary.

Reproduce these internal loop-and-return results with the same build/kernel
commands, using `jet_secp_wnaf_loop`.

`jet_secp_wnaf_prepare.exec_wnaf_post_memset_small` composes the actual scalar
assignment, top-bit reader/branch, loop and return for `0 <= n < 2^255`.
`exec_wnaf_scalar_copy` derives the four destination limb loads from readable
source storage and writable local space using Clight's actual 32-byte
loadbytes/storebytes assignment, not a library-copy premise. The top-bit test
is executed and returns zero from that copied storage. Copying preserves the
output array's zero loads and writable access, and the resulting phase exposes
the final scalar/array state, carry range, weighted equation, return bound,
all memory permissions, allocation frontier and loads outside the local scalar
and output blocks. The small-bound reconstruction conclusion is preserved.

This starts after the original external `memset`; zero cells, the actual
initial temporaries and writable local storage are still premises at that
internal boundary. The `n < 2^255` branch covers both 128-bit split values used
by `generate`, but the original high-top-bit/negation branch is not proved by
this phase. Reproduce with the same build/kernel commands, using
`jet_secp_wnaf_prepare`. No whole wNAF function, literal point-program
correspondence or public jet is registered. Remaining obligations include
entry/initial-temporary establishment and local freeing, the external call,
the other sign branch, composition with the actual split caller/storage,
precomputed tables/startup, the point-operation loop, literal bridge and public
lifecycle above. Coverage remains 505/533.

Next prioritize exact digit correspondence with the fixed literal `wnaf15`
program in `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs`, for each of the
two 128-bit split values. The bridge must identify the complete 129-digit
vector, its order and signed encoding, and connect it to the actual C
recurrence. Weighted reconstruction and odd-digit bounds alone do not identify
that vector. This is independent of the external-call boundary and is needed
before composing the literal `generate` point loop. The generic high-top-bit
branch can wait: it is not needed for these split values.

`jet_secp_wnaf_literal` now ports that program structurally and proves its
parametricity and exact 129-digit, most-significant-first vector order via
the sequential one-bit recurrence. The digits are raw signed Word16 values,
not table indices. Its shift-value and even-step lemmas reuse the verified
word projection/shift adapters; all 21 exported lemmas are closed. Normal
build, recursive kernel checking and focused no-update assumption/contract
comparisons pass. Reproduce with
`JET_TARGETS=C/jet_secp_wnaf_literal.vo bash Coq/build-jets.sh -j1` and
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_wnaf_literal`.
This is not a public jet theorem: still connect the odd signed digit and
skipped zero positions of the C recurrence to this exact literal vector,
then compose the point loop. Weighted reconstruction alone is insufficient.

`jet_secp_wnaf_literal_skip.exec_wnaf_literal_skip` now connects each C skip
dispatch (including its actual scalar-reader call and cursor increment) to
the exact literal zero-digit step. With the literal state's unsigned payload
representing `n / 2^bit + carry`, it derives the next payload
`n / 2^(bit+1) + carry` for either valid carry, without assuming execution or
an output representation. Its pure residual identity is closed; execution
uses the same six inherited assumptions. Normal build, recursive kernel
checking and focused no-update assumption/contract comparisons pass; use
the commands above with `jet_secp_wnaf_literal_skip` in place of
`jet_secp_wnaf_literal`. Odd-digit next-state/encoding and full-vector
composition remain unfinished.

`jet_secp_wnaf_literal_mask.exec_wnaf_literal_digit15` executes the original
full 15-bit window reader and digit store, deriving that the stored signed
integer equals the exact literal step's raw Word16 digit. The pure mask,
low-word projection, oddness and residual-word bridges are closed; execution
retains six inherited assumptions. Normal build, recursive kernel checking
and focused no-update assumption/contract comparisons pass; reproduce with
the same commands using `jet_secp_wnaf_literal_mask`. The endpoint needs
the current positive literal payload represented by `n / 2^bit + carry`;
it derives the digit, not the literal next state. Truncated final windows,
the odd next-state equation and full-vector composition remain unfinished;
there is no new public-jet coverage.

`jet_secp_wnaf_literal_state.literal_wnaf_sub128_positive` discharges the
literal signed-subtraction substep: when the mathematical result is in
`[0, 2^128)`, the original port's output sign bit is zero and its payload is
exactly that result. Both exported lemmas are closed and pass normal build,
recursive kernel checking and focused no-update assumption/contract checks
(same commands with `jet_secp_wnaf_literal_state`). Next combine this with
the signed extension and shift of the emitted digit to establish the whole
odd next-state equation, then handle the skipped positions and truncated
windows before identifying the complete C array with the literal vector.

`jet_secp_wnaf_literal_next.literal_wnaf15_odd_next` now proves that complete
literal odd-step equation for every positive Word128 payload: the next sign
is zero and the next value is `(payload - signed_digit) / 2`, with the exact
literal raw digit. The extension, shifted sign and subtraction premises are
all discharged, not assumed. All 13 exported lemmas are closed. Normal
build, recursive kernel checking and focused no-update assumption/contract
comparisons pass (same commands with `jet_secp_wnaf_literal_next`). Next
connect a C window jump to that odd step followed by the intervening literal
zero steps; then discharge the final truncated-window case and compose the
whole array/vector invariant. The point loop remains a subsequent obligation.

`jet_secp_wnaf_literal_zeros.literal_wnaf_window15` proves the full C-sized
window's literal transition: the odd digit followed by fourteen zero digits,
with next value exactly `n / 2^(bit+15) + new_carry`. Its generic
`literal_wnaf_zero_power` derives arbitrary intervening zero runs.
`jet_secp_wnaf_literal_tail.literal_wnaf_last_window` proves the final short
window using the scalar top bound before adding carry, including the case
`bit=128, carry=1`; it derives a zero final residual and C carry. All six
exported lemmas are closed. Normal builds, recursive kernel checking and
focused no-update assumption/contract comparisons pass. Reproduce with the
same commands using `jet_secp_wnaf_literal_tail` (which includes zeros).

A read-only Astra Medium strategy review confirmed these boundaries match
the actual `len=129, w=15` split128 calls. Do not infer vector identity from
weighted reconstruction: the current array/loop endpoints hide branch jump
equations and visited-prefix spacing. Next add a branch-exact execution
wrapper using `exec_wnaf_dispatch_skip`, `exec_wnaf_dispatch_nonzero` and
`exec_wnaf_nonzero_body`, reusing `wnaf_array_skip`, `wnaf_array_store` and
memory-effect lemmas. Lift it through the existing decreasing-fuel loop
skeleton with an additive invariant carrying the raw literal prefix and
current Word128 residual. Target `exec_wnaf_loop_zero_literal15`: retain
the actual loop/return, complete array and framing conclusions and add
decoded literal digits equal to the reversed 129 C array entries. The final
canonical scalar-normalization/split caller composition and external memset
boundary remain separate, as does the generator point loop.

`jet_secp_wnaf_literal_window.exec_wnaf_literal_split_window` now packages
actual C reader/digit/store execution with the complete literal segment and
next residual for every full or final window reached by a split128 scalar.
It derives the memory store/load from the execution helpers, not from an
execution premise. Its pure dispatcher is closed; execution retains six
inherited assumptions. Normal build, recursive kernel checking and focused
no-update assumption/contract comparisons pass; use the same commands with
`jet_secp_wnaf_literal_window`. This remains a window-level theorem, not the
whole-loop array/vector correspondence or public `generate` equivalence.

`jet_secp_wnaf_literal_body.exec_wnaf_literal_nonzero_body` and
`exec_wnaf_literal_zero_body` now retain the branch-exact data needed by that
loop invariant while executing the complete original C body. The nonzero
endpoint includes the dispatch reader, clamping, digit/store, counter update,
exact new carry/last index, scalar preservation, memory effect and matching
literal window; the zero endpoint retains unchanged memory/carry and a
one-bit advance matching the literal zero step. Both endpoints retain six
inherited assumptions, with no new libc model or execution premise. Normal
build, recursive kernel checking and focused no-update assumption/contract
comparisons pass; use the same commands with `jet_secp_wnaf_literal_body`.
The next missing result is the additive array/vector loop invariant and its
decreasing-fuel induction, not another proof of either body's C execution.

`jet_secp_wnaf_literal_array` supplies closed array-slice/decoded-list
transport lemmas. `jet_secp_wnaf_literal_step.exec_wnaf_literal_array_step`
now preserves the complete visited prefix and matches the newly visited C
array cells to the exact literal segment, including zero carry on reaching
the end. Normal builds, recursive kernel checking and reviewed focused
no-update assumption/contract comparisons pass (use
`jet_secp_wnaf_literal_step` with the same commands above). The execution
retains six inherited assumptions and no added execution/libc premise.

`jet_secp_wnaf_literal_loop.exec_wnaf_loop_zero_literal15` now proves the
actual complete loop and original return for zero-initialized 129-cell arrays
and every positive Word128 payload (including zero). Its output array equals
the decoded fixed literal `wnaf15` vector in reverse index order. It derives
zero final carry, the exact return bound and array/scalar/memory preservation;
the proof no longer relies on weighted reconstruction to identify digits.
The bounded induction also preserves every completed array prefix. Normal
build, recursive kernel checking and focused no-update assumption/contract
comparisons pass (same commands using `jet_secp_wnaf_literal_loop`); all four
exports retain six inherited assumptions and no added model/execution premise.
This closes the loop/vector obligation, not function entry, zeroing/freeing,
the scalar-normalization/split caller composition or the generator point loop.

`jet_secp_wnaf_literal_prepare.exec_wnaf_post_memset_literal15` now composes
the actual by-copy scalar assignment, top-bit/sign-selection call, full loop
and original return against the decoded literal vector. It derives the
scratch scalar, zero final carry, array result, return bound, permissions and
framing from the stated internal boundary. Normal build, recursive kernel
checking and focused no-update assumption/contract comparisons pass (same
commands using `jet_secp_wnaf_literal_prepare`); execution retains six
inherited assumptions, no extra external model. Caller zeroed cells and
initial temporaries remain explicit premises at this post-memset boundary.

The actual public `generate` path is `simplicity_generate -> ecmult ->
strauss_wnaf` with `num=1`, not a substituted `num=0` call. Its static scalar
`na=0` makes the first processing loop skip the arbitrary-point path, leaving
`no=0` and `Z=1`. The earlier loop-development notes above are historical:
`jet_secp_generator_point_stage` now composes the original infinity setup,
literal-aware descending point loop and final Z correction from represented
digit arrays. `jet_secp_generator_entry_split` establishes the actual Strauss
entry, nine owned/distinct locals, preparation, Z=1 and literal scalar halves.
`jet_secp_generator_wnaf_setup` now executes both actual wNAF calls, return
assignments and maximum-length updates, retaining both literal arrays and
read-only generator tables, conditional only on the original zeroing steps.
`jet_secp_generator_function.eval_generator_strauss_from_owned` now composes
the whole original Strauss call: actual entry/preparation, table readiness
through that prefix, the guarded scalar branch, both wNAF calls, complete point
stage and all nine local frees, against the complete literal `generate` tree.
`jet_secp_ecmult_generator.eval_ecmult_generator` now composes the enclosing
ecmult call, including four actual local allocations, all state stores and
all four frees, retaining the exact literal result and initial read-only
globals. `jet_secp_generator_startup` establishes and transports the actual
zero auxiliary scalar and both generator tables from program initialization.
`jet_secp_generate_lifecycle.eval_generate_initialized` now composes the
original public source-frame copy, scalar reader, that ecmult call, point
writer, return and three public local frees for arbitrary valid frames and
cursors. `jet_secp_generate_local.generate_initialized_local_spec_from_memset_steps`
exports the full existing initialized local contract. Its
`generate_runs_from_actual_init` constructs the frames for every Word256 input
from actual initialized program memory and proves startup-state preservation,
so the joint premises are not merely postulated. No scalar/curve restriction
or input/global separation premise is added.

This completes the public `generate` composition at the explicitly deferred
original memset boundary. No wNAF, split, table, loop, reader, writer or public
execution is assumed. Reuse this path for subsequent jets rather than redoing
it; do not assume the table/specification correspondence. External memset
remains deferred and no public `generate` coverage increase is claimed.
The exact current conditional boundary and reproducible checks are recorded in
`JET_SECP_EXTERNAL_MISMATCHES.md` under Generation.

## Active `swu` frontier

`jet_secp_swu_root_power` connects the already-verified literal square-root
chain to the exact exponent `(feP+1)/4`, then uses the checked field-primality
certificate to prove that this literal root and the corresponding C root-check
flag succeed on every represented square. It covers arbitrary Word256 inputs;
there is no candidate-success premise or new primality assumption.

This closes a prerequisite, not the public mapper. The C helper uses the third
candidate without testing its flag, whereas the canonical literal mapper tests
it. The subsequent checkpoints below discharge that numeric selection
obligation, including zero inputs. This difference in control flow is not
evidence of a mismatch. Connect the candidate algebra to the actual C helper
and literal program before composing the public frame wrapper. Do not assume
third-candidate success to obtain a public theorem. The existing explicit ctz
boundary remains deferred; no new external model or coverage row is added.
Coverage remains 514/533. Reproduce the normal build and recursive kernel
check with the commands in `JET_SECP_EXTERNAL_MISMATCHES.md`, using
`C/jet_secp_swu_root_power.vo` / `C.jet_secp_swu_root_power`.

`jet_secp_swu_selection` further proves that `t*t+8` is nonzero modulo the
field prime for every integer input, by a closed modular-exponentiation
certificate that -8 is a nonsquare. It also proves
`swu_third_root_check_from_product`: if the product of three represented
root-check inputs is a square, failure of the first two actual literal checks
forces success of the third. The character argument discharges all nonzero
conditions from those failures, rather than restricting inputs. The candidate
numerator polynomial identity is checked separately with `ring` (also explored
through the restored isolated rocq-mcp backend).

At this intermediate checkpoint the square-product hypothesis had not yet
been established for the exact source candidates. The later result below
discharges that numeric obligation; neither checkpoint is a public theorem.
Build/check this module with the same
commands using `C/jet_secp_swu_selection.vo` / `C.jet_secp_swu_selection`.

`jet_secp_swu_candidates` now proves the square-product identity for the exact
hexadecimal C constants and joint-inverse formulas on every nonzero field
input. The zero-input branch is handled separately: the first candidate
already has a square radicand. `swu_c_candidates_third` covers **all** inputs
and forces success of the third actual literal root check when the first two
fail, given numeric representations of the three source radicands. It assumes
neither candidate success nor a nonsquare-denominator fact. The constant `c`
is checked against the exact modular root exponent, not an arbitrary choice of
square root. Modular field automation uses the existing proved `modInv` and
field-primality certificate; no new field or inverse axiom is introduced.

The later literal bridge below establishes the three representations for the
canonical term. They must still be established through actual C helper calls,
not retained as public jet premises. The explicit original ctz boundary is
still deferred. Coverage is
514/533, not a new public SWU proof. Build/check with the same commands using
`C/jet_secp_swu_candidates.vo` / `C.jet_secp_swu_candidates`.

`jet_secp_swu_literal` now ports the exact canonical candidate, selection and
parity tree (LibSecp256k1.hs:709--733). Its constants follow the canonical FE
modular-power and halving computations; closed proofs identify their values
with the C constants. Its parametricity proof is closed. The third root test
and `(0,0)` failure branch are retained in the port, not removed by definition.

`jet_secp_swu_literal_bridge.swu_literal_candidates_c` connects that term's
candidate values to the C joint-inverse formulas on every Word256 input.
`swu_joint_inverse_opposite` proves the inverse-sign bridge, including zero.
`swu_literal_third_check` discharges the third-test-success obligation for
the exact literal candidates with **no representation or success premise**.
`swu_literal_select_no_fallback` and `swu_literal_selected_step` then derive
the three-way selected literal point and original final parity correction;
they prove the canonical fallback unreachable rather than changing the term.
The literal-program bridges inherit only functional extensionality; the new
inverse-sign fact is closed. No new library model is declared.

Next execute the original `f_shallue_van_de_woestijne` call: thirteen owned
40-byte field locals, the actual global constants, all field calls and copies,
three root calls, conditional moves, point setup, parity correction and frees.
Use the numeric bridge above to relate those results, then compose the public
reader/writer wrapper. Only the previously deferred original ctz steps may
remain conditional; do not introduce premises for internal call execution,
candidate success or the final literal equality. Coverage remains 514/533.
Reproduce the targeted normal build/kernel check with
`C/jet_secp_swu_literal_bridge.vo` / `C.jet_secp_swu_literal_bridge` and focused
assumption/contract comparisons for these two modules and `jet_secp_swu_candidates`.

`jet_secp_swu_startup` now derives the actual `negc` and `d` limbs, their
numeric values and exact readonly bounds from `Genv.init_mem jets_secp.prog`.
It combines those constants with the existing field-inversion modulus state,
proves initialization exists and proves preservation through the existing
readonly-preservation contract. Fresh owned storage is automatically separate
from all three globals; no input/global separation premise is introduced.

`jet_secp_swu_constant_product.eval_swu_constant_product` executes the original
three-address C multiply into an uninitialized private field, with the
initialized constant as a **readonly** first operand. It reuses the existing
field-product symbolic state, u128 log and proved actual-C oracles, deriving
the input relation from storage rather than assuming it. It returns the exact
stored limbs, tight bounds, ownership, numeric product, startup preservation
and memory frame. The constant is never made writable in the proof.

`jet_secp_swu_initial.exec_swu_initial` composes the actual helper's first two
calls (`wd=t^2; x1=negc*wd`), identified in its unchanged body by
`swu_initial_source`. It derives both calls from owned caller storage, retains
the input, all three owned fields, exact product, result bounds, startup state
and old-memory framing. Its C execution inherits the usual six assumptions;
there is no extra execution, result or external-helper premise at this prefix.

Next continue **that same body** from `swu_after_initial`: the `x3d=wd` struct
copy, multiply by 3, magnitude-3 negation, add 8 to wd, multiply the joint
denominator and invoke the already-proved original inversion with explicit
ctz steps. The rest of the candidate calls, roots, conditional moves, point
setup, parity correction, helper allocations/frees and public wrapper remain
open. This prefix is not public SWU coverage: the count stays 514/533. Build
and recursively check using `C/jet_secp_swu_initial.vo` /
`C.jet_secp_swu_initial`, and compare focused assumption/contract records for
`jet_secp_swu_startup`, `jet_secp_swu_constant_product` and `jet_secp_swu_initial`.

The shared `jet_secp_field_add_int` now generalizes the original fixed-7
execution pattern to every C int, reusing `mul_small_initial` for the owned
input relation. Its small-addition corollary derives the exact numeric sum,
stored limbs, ownership, reusable bounds and frame for constants from 0 to 8;
in particular it supplies the actual additions by 8 and 1 above. Signed
conversion and machine wraparound are explicit in the unrestricted theorem;
the numeric theorem proves no overflow from its bounds. This is helper
execution, not additional public coverage. Build/kernel-check
`C/jet_secp_field_add_int.vo` / `C.jet_secp_field_add_int` and compare its
focused assumption/contract records.

`jet_secp_field_negate_magnitude` likewise executes the original in-place
`fe_negate` with a parameterized magnitude, sharing `mul_small_initial`
instead of duplicating region construction. The unrestricted storage theorem
retains C's machine operations. `eval_negate_mag_bounded` proves exact
`2*(m+1)*p-input`, stored limbs, ownership, reusable bounds and framing for
magnitudes 0..7 with a proved subtraction bound. `negate_mag_scaled_input`
discharges that bound for `fe_mul_int(m)` applied to tight limbs: instantiate
m=3 after the SWU copy and multiply. This does not substitute a magnitude-one
call. Compose these steps plus the parameterized addition into
`swu_after_initial` next; no new public jet is registered. Build/kernel-check
`C/jet_secp_field_negate_magnitude.vo` /
`C.jet_secp_field_negate_magnitude` and compare its focused records.

`jet_secp_swu_joint_setup.exec_swu_joint_setup` now composes those actual four
statements from `swu_after_initial`, preserving the original `7+1` AST and
magnitude-3 argument. From tight owned wd and an uninitialized owned x3d it
derives both stored results, exact `wd+8` and `8*p-3*wd`, reusable bounds,
ownership, unchanged other memory and startup preservation. No execution or
output premise is retained. The trailing skip is a proof prefix endpoint;
`swu_joint_setup_source` and the existing prefix-composition lemma reconnect
it to the unchanged original suffix.

`jet_secp_swu_joint_inverse.exec_swu_joint_inverse` extends that execution
through the original three-address joint product and in-place `fe_inv_var`.
It derives storage for all three fields, their ownership, result bounds,
the exact inverse `modInv ((wd+8)*(-3*wd)) p`, startup preservation and frame.
Its **only deferred execution premise** is the same exact original CTZ call
contract used by `eval_fe_inverse_var_slice`; no new external model or
replacement implementation is introduced. The module is conditional helper
execution, not accepted public SWU coverage. Its closed congruence lemma
identifies the inverse with `swu_joint_inverse t` whenever incoming wd
represents `t*t` modulo p, including zero. Setup and inversion both inherit
the usual six assumptions; inspect the quantified CTZ premise in the
contract, not just the assumption list.

`jet_secp_swu_before_candidates.exec_swu_before_candidates` composes this
six-statement prefix with `exec_swu_initial`: all original first eight
statements now execute from input storage and initially uninitialized
intermediates. It derives tight square bounds from `square_output_bounds`,
retains the original input and initial x1 storage, and derives the actual
inverse's exact equality to `swu_joint_inverse (radix_value input)` using
`square_output_numeric` and `swu_joint_inverse_congruent`. It returns all five
owned fields, value/range facts, initialized globals, unchanged other memory
and readonly preservation. No square/denominator representation or internal
call is assumed. The original CTZ contract remains explicit; the result is
still a conditional **prefix**, not a whole-public theorem.

`jet_secp_swu_constant_add.eval_swu_constant_add` now executes the original
in-place `fe_add` with either initialized SWU constant as a readonly right
operand. It reuses the existing addition state and shared sum lemmas, deriving
the owned/borrowed representation from actual storage. It returns exact
stored limbs, numeric sum, magnitude-two bounds, ownership, unchanged other
memory and startup/readonly preservation. No writable-global, separation,
execution or output premise is assumed.

`jet_secp_swu_first_candidate.exec_swu_first_candidate` composes the actual
next three calls: x1*=x3d; x1*=jinv; x1+=d. It derives their execution from
owned storage, preserving x3d/jinv and their ownership, deriving both modular
value and reusable bounds. `exec_swu_through_first` then composes **all first
eleven original statements from input storage**, derives x3d's square-model
value and connects the stored x1 to `swu_c_candidate1 (radix_value input)`.
Input, wd, x3d and jinv storage are retained, all five objects remain owned,
and startup/readonly preservation and old-memory framing are derived. The
unchanged CTZ contract remains explicit; this is still a conditional prefix,
not registered public coverage. Its source-tree equalities retain the
original statement order and original suffix.

`jet_secp_swu_second_candidate.exec_swu_second_candidate` executes the
original copy x1 to x2, add-one, and magnitude-3 negation. The no-wrap and
subtraction bounds follow from the preceding proved `field_scaled_bounds 2`;
no normalization, magnitude-one substitution or assumed intermediate output
is used. It derives x2's exact radix value `8*p-(x1+1)`, reusable bounds,
ownership and preservation. `exec_swu_through_second` composes **all first
fourteen original statements from input storage**, retains all six owned
fields, and establishes both `swu_c_candidate1` and `swu_c_candidate2` modulo
p as well as the exact joint inverse, startup state, readonly preservation
and memory frame. The same original CTZ contract remains explicit; neither
result is whole-public SWU coverage.

`jet_secp_swu_third_candidate.exec_swu_third_candidate` executes the original
square wd into x3, multiply x3 by wd and jinv, then add 1. It derives the
numeric value, magnitude-two and loose square bounds, ownership, unchanged
wd/jinv, startup/readonly preservation and framing. `swu_add_int_scaled` is
shared for bounded small additions (including the later add-seven).
`swu_setup_wd_square` derives wd's loose bounds and numeric value from the
input square, not a representation premise. `exec_swu_through_third`
composes **all first eighteen original statements from input storage** and
establishes all three `swu_c_candidate` values modulo p while retaining all
seven owned fields and the exact joint inverse. Its source equality preserves
the unchanged statement tree and suffix. The same CTZ contract remains
explicit; this is a conditional prefix, not whole-public SWU coverage.

`jet_secp_swu_cubics.exec_swu_cubic` shares the original square/multiply/add-7
execution proof across the three radicands; `exec_swu_cubics` composes all
nine calls. It derives bounds, values, unchanged candidates, ownership,
readonly preservation and framing from loose input bounds and uninitialized
owned output storage. `jet_secp_swu_before_roots.exec_swu_through_cubics`
composes **all first twenty-seven original statements from input storage**,
retaining all ten fields and deriving the three cubic values from the input.
Its source equality preserves the exact original suffix.

`jet_secp_swu_root_inputs.swu_root_inputs_match` connects those modular
radicand values to the exact literal Simplicity root inputs, for any input
`root_words_match w t`. The candidate formulas respect modular equality
(including inversion at zero); no exact raw-input equality or canonical-limb
assumption is needed. This matters because the original reader normalizes
modulo p. Instantiate the existing `eval_root_function` with these matches,
not its reader-only corollary. These are still conditional prefix results,
not public SWU coverage; the original CTZ contract remains explicit.

`jet_secp_swu_roots.exec_swu_roots` composes the three original
`fe_sqrt_var` calls using that loose-input helper theorem. The two saved
flags retain the exact generated `Scall (Some _t'1); Sset _alphaquad` and
`Scall (Some _t'2); Sset _betaquad` trees; the third call discards its flag.
The output environment has proved flag lookups and preserves other temps.
Root coordinates and check flags match the literal root program, with
ownership, old-memory framing and readonly preservation derived from calls.

`jet_secp_swu_before_selection.exec_swu_through_roots` composes this with
the entire input-driven prefix, discharging the three root-input relations
from the earlier radicand results. It retains the input and all six candidate
coordinates, bounds, all thirteen input/private allocations, startup and
frames. Its final relations connect the three X coordinates, Y root values
and flags directly to the literal candidates. It adds no execution oracle;
the same original CTZ contract remains explicit. These are still conditional
prefix results, **not public SWU coverage**.

`jet_secp_field_cmov.eval_field_cmov` now executes the original five-limb
masked move for flag 0 or 1. It proves exact word selection, unchanged
source, both objects' ownership, framing and readonly preservation without
arithmetic bounds or a library premise. `jet_secp_swu_select_exec.exec_swu_select`
uses it for all four actual SWU calls, evaluating the original not/and
expressions from alpha/beta temps and preserving their statement order.
It produces `swu_selected_words` for both coordinates and retains all six
objects. These are actual call/statement execution proofs, not call oracles.

`jet_secp_swu_selected_literal.swu_selected_matches_literal` links those
selected serialized coordinates to `swu_selected_candidate t`, using the
literal candidate/flag relations already derived by the input-driven prefix.
It proves canonicality for the literal add/negate outputs; it does not assume
canonical C limbs or silently identify a raw p word with 0.
`jet_secp_ge_set_xy_separate.eval_ge_set_xy_separate` proves the original
affine constructor with separately stored X/Y, as SWU actually calls it.
It reuses the actual Clight struct-copy proof, keeps the flag store, and
derives output ownership, unchanged permissions, framing and readonly
preservation. No repacking, alternate C implementation or memcpy premise
is introduced. The old same-input-block theorem remains intact.

`jet_secp_root_output_bounds.root_chain_candidate_tight` derives the tighter
root-output bounds from the last checked square in the root chain.
`exec_swu_through_roots` now returns these bounds for all three Y candidates;
this strengthens its conclusion without adding any input premise. Loose
`square_input_bounds` alone do not justify the final magnitude-1 negation.

`jet_secp_swu_parity_fields` executes the original separate-output negation
and conditional move with Y at point+40, preserving X, infinity, and the
whole point allocation. Its symbolic Y region uses `u64_cells 40` with
ownership `Some 88`, base 0; it does not assume a separate allocation at +40.
`jet_secp_swu_parity.exec_swu_parity` composes all three original suffix
calls, including the real input oddness test, in both parity cases. The
oddness test needs the exact normalized reader representation, not just
equality modulo the odd prime: adding p could change parity.
`swu_parity_of_selected_matches` identifies the serialized output with the
literal Simplicity SWU term, retaining normalization of X in literal
`ge_negate` rather than silently dropping it.

`jet_secp_swu_body.exec_swu_body` composes the entire original statement
body from `square_reader_rho t`, uninitialized owned locals and an owned
output point. It derives final X/Y storage and loose bounds, the zero
infinity flag, equality to `literal_swu t`, ownership, startup preservation,
old-memory framing and readonly preservation. No intermediate call,
selection, parity, output relation or new library contract is assumed.
The original CTZ call contract remains explicit. This is a conditional
**complete statement-body** theorem, not function-entry/freeing or public
jet coverage.

`jet_secp_swu_function.eval_swu_function` now composes the entire original
helper call. It derives function entry, all thirteen fresh 40-byte local
allocations in the actual `fn_vars` order, the separation and ownership
needed by `exec_swu_body`, and the exact original `blocks_of_env` frees.
It keeps the caller's reader allocation and output point, derives stored
X/Y and bounds, the zero infinity flag, equality to `literal_swu t`, startup,
readonly preservation, and old-memory framing outside the two caller
objects. No allocation, freeing, internal call or output is assumed. The
only non-storage premises remain the established startup state and original
CTZ call contract; this helper is not the public read/write wrapper.

`jet_secp_swu_public_boundary` and `jet_secp_swu_public_body` now prove the
original public entry, exact statement tree, call resolution and original
free list. The source-frame-copy adapter changes only the local environment
used by its execution derivation; it reuses the existing decompression
allocation, source-copy and frame facts. It does not substitute a runtime
implementation or reorder the actual frees.
`jet_secp_swu_public_rest` derives the canonical reader, complete mapper and
original affine writer from general frames and owned uninitialized locals.
It preserves startup across the reader and writer with the existing internal
helper-table proof. Its generic affine encoding/writer lemmas keep the
literal result relation separate from serialization. The checked scalar-level
`swu_limb_list_words` lemma avoids costly kernel conversion of the full
256-bit normalization term: instantiate that opaque integer-level equality
in `swu_reader_digits`, rather than using a beta-expanded `generalize` proof
or directly converting `normalized_value t` to `point_canonical_limbs t`.
The latter completed its tactics but exceeded the bounded final kernel
check; the factored proof compiles with the original 10-second limit.

`jet_secp_swu_public_call.eval_swu_literal_public` composes all original
public allocations, the source-frame copy, every body call, true return
conversion and frees, with startup, readonly and memory-frame preservation.
`jet_secp_swu_local.swu_initialized_local_spec_from_count_calls` now states
the complete existing initialized local contract for `simplicity_swu`
against `literal_swu`: every Word256 input, exact 512-bit output, arbitrary
valid cursors, output-prefix/cursor and unaffected-load guarantees, and
startup preservation. No input canonicality, curve, nonzero, initialized
output or additional separation premise is exposed. This remains explicitly
conditional on the same deferred original CTZ call contract and startup
state; it is not a new accepted row.

The implementation/specification composition is now complete under those
explicit shared obligations. Next continue independent jet obligations as
requested, keeping SWU unregistered until CTZ and the real startup-call
linkage are justified under the accepted policy. `swu_startup_initial` and
`swu_startup_exists` already establish the globals at `Genv.init_mem` of the
original program; do not replace a real caller/startup argument with an
assumed output, alter the external-call relation or broaden coverage merely
because the conditional local theorem compiles.

Coverage stays 514/533; these are not whole-public SWU registration.
Reproduce the normal build with
`JET_TARGETS='C/jet_secp_swu_local.vo'`
and kernel check with
`-o C.jet_secp_swu_local`, plus focused assumption/contract comparisons for
`jet_secp_root_output_bounds`, `jet_secp_swu_before_selection`,
`jet_secp_swu_parity_fields`, `jet_secp_swu_parity`, `jet_secp_swu_body` and
`jet_secp_swu_function` and `jet_secp_swu_public_{boundary,body,rest,call}` /
`jet_secp_swu_local`.

## Active `hash_to_curve` frontier

The exact public target is `f_simplicity_hash_to_curve` against Haskell's
`hash_to_curve = assert hash_to_curve_core` (LibSecp256k1.hs:729--742,
836--837). No previous generator load/save execution proof was found in
the current ordinary or experimental Coq sources. Its main path is input
byte reading, `generator_generate` with NULL blinding, two prefixed SHA
computations and two SWU calls, mixed addition and affine conversion,
generator save, generator load and affine writing. The SHA functions are
internal in the frozen secp unit; reuse/transport their existing proofs,
not a different generated program or an external SHA oracle.

`jet_secp_generator_load` now executes the entire original
`secp256k1_generator_load`, including both set_b32 calls, retained verification
loops, ignored conversion flags and infinity=0 store. It reuses the original
symbolic executor and the existing set_b32 expressions. The source is the
actual owned 64-byte local generator, not the unrelated readonly generator
tables used by ecmult. Neither source nor output is assumed initialized
beyond the source byte loads.

`jet_secp_generator_load_values` reuses `sb_output_numeric` and its checked
machine-value bounds for both coordinate halves. `generator_zreg_den` shares
the denotation bridge for a checked integer-valued cell list, and the paired
valuation has a proved connection to the physical concatenated byte array.
`jet_secp_generator_load_storage.eval_generator_load_from_storage` derives
the actual call from two arbitrary 32-byte halves, initial typed loads and
separate owned allocations. It returns the exact raw 256-bit X/Y limbs,
zero infinity flag, both allocations, unchanged source bytes, outside-block
framing and readonly preservation. There is **no** field-value-less-than-p,
curve, initialized-output, CTZ or libc premise.

`jet_secp_generator_load_write.eval_generator_load_write` composes this with
the original affine writer for arbitrary valid destination frames/cursors.
It derives the exact encoded coordinate pair, ownership, memory frame and
readonly preservation. Its value lemma identifies each serialized coordinate
as the corresponding big-endian source integer modulo p. It reuses the
already checked integer-level limb-list equality and generic affine writer
from the SWU caller proof, avoiding the normalization-conversion slowdown.
This is the actual final load/write span, not a whole-public hash_to_curve
theorem or a registration. Coverage remains 514/533.

`jet_secp_generator_save` now executes the full original saver, retaining its
one-iteration infinity inspection and both normalization/get_b32 calls.
The initial infinity flag is an arbitrary machine int, not required to be zero.
`jet_secp_generator_save_values` identifies all four branch outputs with the
existing writer expressions, then reuses `wide_write_selected_machine_bytes`
to derive the two exact 32-byte big-endian coordinate residues modulo p.
It uses an explicit selected-leaf projection to avoid expanding unrelated
symbolic conditionals while matching the representation.

`jet_secp_generator_save_storage.eval_generator_save_bytes` composes actual
execution with physical byte loads of both coordinate halves, unchanged
infinity flag, both owned 88/64-byte allocations, the outside-memory frame and
readonly preservation. Its premises are the initial private-region
representation and bounds <=2^60 on the ten input limbs. No call, expected
output, CTZ or libc behavior is assumed. These are internal caller premises:
the generator caller must establish them from its actual point and allocation.
This result is not yet a whole-public hash_to_curve theorem or new coverage.

`jet_secp_generator_save_initial.generator_save_initial_from_fields` now
constructs that representation from the two concrete coordinate fields, the
loaded infinity flag and ownership of the point and generator allocations.
The destination bytes are not assumed initialized. Its generic field-slice
constructor shares the existing region append and limb-index lemmas.

`jet_secp_generator_codec` proves the exact big-endian save/load round trip:
the 32-byte halves are in range, their decoded values are precisely the
coordinate residues, and the final writer preserves those residues exactly.
The byte/value lemmas are closed and use no hash or cryptographic assumption.
`jet_secp_generator_roundtrip.eval_generator_save_load_write` composes the
three actual C calls from the concrete initial fields, flag, owned allocations
and limb bounds. It derives the final 512-bit encoded coordinate pair,
arbitrary-valid-cursor output invariant, ownership, memory frame and readonly
preservation. Every intermediate byte load and frame fact is established by
the preceding call, not assumed as a postcondition.

`jet_secp_affine_set_infinity.eval_affine_set_infinity_owned` now proves the
original infinity setter from ownership alone: it stores the flag and invokes
both actual field-clearing loops, producing zero coordinates and flag 1.
`jet_secp_affine_infinite.eval_affine_infinite_owned` composes it into the
whole original `ge_set_gej_var` infinity branch for every nonzero machine
flag, including both unused local allocations, early return and local frees.
It preserves source ownership and all pre-existing memory outside the output
point. Source coordinates need not be initialized. Neither theorem requires
CTZ, libc behavior or an assumed helper execution. They do not establish that
hash_to_curve reaches infinity, nor a whole-public result or new coverage.
Build `C/jet_secp_affine_infinite.vo`, kernel-check
`C.jet_secp_affine_infinite`, and run the existing focused assumption/contract
comparisons for both affine infinity modules.

`jet_secp_generator_field_roundtrip.eval_generator_field_roundtrip` eliminates
the private serialization representation and its ten-limb bound from the
caller interface: both follow from actual coordinate fields and their existing
square-input bounds. The exact save/load/write output is the original affine
writer's coordinate pair, with equality proved through its existing residue
lemmas, not a replacement specification.
`jet_secp_generator_affine_roundtrip` then composes four original calls, from
projective storage through affine conversion and generator save/load to the
output frame. The finite theorem derives every intermediate field and bound,
retaining the explicit CTZ condition and initialized modulus state. The infinity
theorem needs neither and derives a zero-coordinate encoding from a nonzero
source flag, without initialized source coordinates. Both establish ownership,
framing and readonly preservation. These are call sequences, not the intervening
generator/public-wrapper statements, SHA execution or a public counterexample.
Build and recursively kernel-check `C.jet_secp_generator_affine_roundtrip` and
compare both new modules' existing focused assumption/contract records.

This is a complete serialization span, not execution of the intervening
generator return/free and public wrapper statements, nor a whole-public
hash_to_curve equivalence. Coverage stays 514/533. The affine-conversion outputs
are now connected; next compose the actual generator/public-wrapper lifecycle
and preceding hash/SWU calls. For the earlier
generator caller, retain both SHA-derived set_b32 flags and every original
operation before its return: C does **not** exit early for a rejected digest.
`jet_secp_swu_raw_input.eval_swu_raw_function` now supplies the whole original
SWU helper execution for every raw Word256 representation, including rejected
digests >=p, retaining the original explicit CTZ condition and actual startup
state. The body and function proofs are shared with the old normalized-reader
theorems, whose statements are unchanged. The generic `field_words_odd` and
`exec_swu_words_parity` results read the low bit actually stored by C, instead
of assuming canonical parity. `swu_raw_accepted_output` identifies the result
with the existing literal SWU result when the digest is below p; no such input
restriction is imposed on the execution theorem. `swu_digest_value` and
`swu_digest_input` connect arbitrary 32-byte set_b32 output limbs to this raw
input contract. Build both `C/jet_secp_swu_raw_input.vo` and
`C/jet_secp_swu_local.vo`, recursively kernel-check the two roots, and compare
the existing focused records for the new modules and SWU body/function/public
chain.

`jet_secp_set_b32_owned.eval_set_b32_owned` now derives the actual set_b32
call, exact comparison flag, raw output limbs, both owned allocations and
unchanged digest bytes from the real 40/32-byte caller storage. It reuses
the existing checked conversion arithmetic. No assumption of a successful
comparison is made.
`jet_secp_generator_digest_mapping.exec_generator_digest_mapping` composes
this with raw SWU and the actual intervening `ret &= flag` statement for both
digest positions. Closed source equalities identify the exact subtrees in the
original generator body. Its final temporary map carries the conjunction of
the prior success bit and the current comparison flag; a rejected digest
leaves ret zero while still executing SWU. The result includes ownership,
digest-byte retention, startup and readonly preservation, and a literal SWU
output equality for accepted digests. The CTZ condition remains explicit.
Build `C/jet_secp_generator_digest_mapping.vo`, recursively kernel-check
`C.jet_secp_generator_digest_mapping`, and compare the two new modules with
the existing focused assumption/contract tools. Next compose the real SHA
blocks, accumulator initialization/addition, function entry and return/free
statements around these stages; the stage alone is not a public hash_to_curve
contract and adds no coverage.

`jet_secp_sha_pure_transport` reuses the existing transport proof and checked
core/SHA bodies for six helpers in the frozen secp program: sha256_iv/init,
ReadBE32, WriteBE32/64 and sha256_fromMidstate. Computed checks establish the
actual function lookups and layout/call compatibility in both source programs;
the closed helper table also yields readonly preservation. This is not a
transport theorem for SHA compression or its dispatch/global accesses.
`jet_secp_sha_owned` instantiates complete initialization and midstate-to-byte
serialization from actual owned storage. Its exact 32-byte list is bounded
in 0..255 and matches the generator digest mapper's byte representation.
`jet_secp_generator_sha_start.exec_generator_sha_start_owned` composes the
original initializer call and actual By_copy assignment for both generator
SHA blocks, identified by source equalities. It derives the context output
pointer, zero counter/overflow, IV words, ownership, framing and readonly
preservation. No libc model or intermediate call is assumed in these results.
The existing SHA dependency objects were rebuilt under the pinned toolchain
after detecting an inconsistent frame-interface cache; proof sources were
not changed to resolve that cache error. Build
`C/jet_secp_generator_sha_start.vo` and `C/jet_secp_sha_owned.vo`, recursively
kernel-check both roots, and compare all three modules' focused records.
`jet_secp_sha_compression` now transports the existing checked portable round
chain into the original secp program. It also derives exact `SHA256.hash_block`
state words, ownership, unchanged block input, framing and readonly preservation
for the actual portable call. `jet_secp_sha_dispatch` reuses the byte-reading
prefix through checked statement transport and then executes the actual mutable
dispatch load and indirect call. Its complete byte-wrapper theorem includes
the private 64-byte array's allocation and free, exact hash-block state, framing
and readonly preservation. It needs no libc or compression oracle.
`jet_secp_sha_startup` establishes the dispatch pointer and counter constant
from the original program's actual `Genv.init_mem`, whose existence is already
proved. It proves the counter cannot be written and the dispatch cell cannot
be owned as Freeable storage. The owned byte-compression theorem composes this
with the real call and preserves startup, deriving global separation from
ownership rather than assuming a final global-state premise. Mutable dispatch
preservation uses the call's framing; readonly preservation alone is insufficient.
Build `C/jet_secp_sha_startup.vo` and `C/jet_secp_sha_compression.vo`, recursively
kernel-check both roots, and compare all three modules' focused records.
`jet_secp_sha_context` reuses the checked context-field layouts by expression
transport and proves the actual low-counter overflow branch. The original
`memcpy_bytes_effect` proof is factored to expose its already-constructed
`Mem.storebytes` witness in `memcpy_bytes_effect_store`; the existing public
interface is unchanged. This permits readonly preservation without assuming
external-call properties or a final-memory invariant.
`jet_secp_sha_absorb_short.eval_secp_sha_absorb_short` executes the complete
original `sha256_uchars` call whenever the current buffer and supplied bytes
total less than 64. It covers empty and nonempty inputs, actual overflow and
counter updates, the loop exit, conditional memcpy, return conversion and
freeing the empty local list. It derives the exact buffered concatenation,
ownership, framing, readonly and SHA-startup preservation. The existing
bounded `memcpy_model` remains explicit; this does not discharge libc linkage.
`jet_secp_generator_sha_absorb` derives both 16-byte prefixes and their readonly
permissions from the actual secp initializer, proves their preservation and
separation from owned contexts, and identifies both call pairs in the frozen
generator body. `exec_generator_sha_absorb_owned` composes those actual prefix
and key calls for every 32-byte key, yielding exactly prefix++key in the
context, counter 48, overflow false, unchanged output pointer, ownership,
framing and preserved startup/prefix state. This is the original internal
caller fragment, not an independently chosen message or a whole-public theorem.
Build `C/jet_secp_generator_sha_absorb.vo`, recursively kernel-check that root,
and compare the three new modules plus `C.jet_sha_uchars_prep` with the existing
focused assumption/contract audits.
`jet_secp_sha_absorb_block.exec_secp_sha_fill_block` now executes the original
loop when the remaining bytes exactly fill the current partial block. It
composes the bounded memcpy, actual pointer/count updates, context output-pointer
read, real compression-wrapper call and reset with the next false loop test.
It derives exact `SHA256.hash_block` registers, zero remaining length, reset
block/delta temporaries, both owned objects, preservation of the context's
non-buffer fields, framing, readonly and SHA-startup preservation. It applies
to every partial-buffer length below 64 and exactly enough remaining bytes;
it does not assume the compression call or its resulting registers.
The shared memcpy-call proof is parameterized by its actual count temporary,
and owned compression permits a byte offset; the previous theorem interfaces
remain unchanged wrappers. This is an internal loop result conditional on
the existing `memcpy_model`, not another whole-public coverage entry.
Build `C/jet_secp_sha_absorb_block.vo` and
`C/jet_secp_generator_sha_absorb.vo`, recursively kernel-check both roots,
and compare the block/startup/short modules' focused records.
`jet_secp_sha_absorb_head.exec_secp_sha_absorb_head` factors the actual
pre-loop setup, through the exact 64-byte boundary, out of the partial-block
proof. It derives the context/array/block/count temporaries, actual counter
and overflow stores, ownership, preservation of buffered bytes and other
loads, framing, readonly and startup preservation. The previous small-overflow
interfaces remain wrappers of the new bounded lemmas, and the partial-block
theorem now reuses this setup with its original statement and assumptions.
`jet_secp_sha_absorb_full.eval_secp_sha_absorb_full` composes actual function
entry, that setup, the checked block-filling loop, zero-length tail, overflow
read, true return conversion and empty local free. It proves exact hash-block
registers, counter 64, false overflow, preserved output pointer, both owned
objects, framing, readonly and startup for every partial buffer completed by
the supplied bytes. The existing `memcpy_model` stays explicit. No helper
execution or final-state invariant is assumed.
Build `C/jet_secp_sha_absorb_full.vo` and
`C/jet_secp_generator_sha_absorb.vo`, recursively kernel-check both roots,
and compare head/full/context records plus the unchanged short/block/generator
records with the existing focused audit scripts. This does not add public jet
coverage.
`jet_secp_sha_u64_full.eval_secp_sha_u64_full` now executes the complete
original `sha256_u64be` caller for every supplied 64-bit word and every
56-byte buffer. It reuses the checked `WriteBE64` through existing validated
transport and the full byte-absorption call. The proof includes its actual
8-byte allocation, serialization, call, return conversion and free, exact
hash-block registers, counter 64, false overflow, output pointer, both owned
objects, framing, readonly and startup preservation. No stored byte, intermediate
call or final global invariant is assumed. The existing bounded `memcpy_model`
remains explicit, and no coverage is added. Rebuild
`C/jet_secp_sha_u64_full.vo`, recursively kernel-check
`C.jet_secp_sha_u64_full`, and compare its focused assumption/contract records.
`jet_secp_sha_finalize48.eval_secp_sha_finalize48` now executes that original
finalizer for every 48-byte buffered message and every eight-word state.
The existing proof of all 64 padding-array stores is reused by checked
statement transport, and both actual absorption callers are composed. The
theorem includes the original 64-byte array allocation, saved return flag,
bit-length calculation, padding count, all calls, return conversion and free.
It derives exactly `SHA256.hash_block regs (be_words (l ++ sha_pad 48))`,
counter 64, false overflow, unchanged output pointer, ownership, framing,
readonly and startup preservation. `memcpy_model` remains explicit; no source,
AST, specification, generation setting or public coverage row is changed.
Build `C/jet_secp_sha_finalize48.vo`, recursively kernel-check
`C.jet_secp_sha_finalize48`, and compare its focused records.
`jet_secp_sha_bytestring48.secp_sha48_bytestring` now connects the exact
register formula to `Digest.byteStringHash` for every 48-byte message. It
reuses the ordinary byte/word conversion proof and existing SHA functional
bridge; no host hashing oracle or archived environment-unit execution is
imported. `jet_secp_generator_sha_complete.exec_generator_sha_block_owned`
composes the actual initialization/copy, both absorption calls, finalization
and digest serialization for each of the two original generator SHA spans.
It derives exact digest bytes and registers, preserves all four owned local
objects and framing, and re-establishes SHA startup and readonly prefix state.
The corollary `exec_generator_sha_block_bytestring` connects that actual
statement execution and memory result directly to
`Digest.byteStringHash (prefix ++ key)` for every 32-byte key, retaining the
same ownership, framing and preservation conclusions. No digest-below-p or
other key-value restriction is introduced. The existing `memcpy_model` remains
explicit, and no public coverage row is added.
Build `C/jet_secp_generator_sha_complete.vo`, recursively kernel-check that
root, and compare both new modules' focused records. Rebuilt byte-writer,
hash-serialization and pure byte-block dependency records must still match.
`jet_secp_generator_hash_literal` ports each exact `hashBlock` expression
inside Haskell's `hash_to_curve_core`: the appropriate 16-byte prefix,
the two input halves, the `2^127 + 128 + 256` postfix, and the canonical IV.
`generator_sha_regs_literal` identifies the original generator's computed
registers with that Simplicity expression. `generator_digest_word_literal`
identifies the word consumed by SWU, and `generator_digest_value_literal`
identifies its full numeric value for C's conversion acceptance test.
The shared byte-vector decoding lemma works at every vector depth; the
existing word/vector cast and serialization lemmas are reused. These bridges
cover every Word256 key without assuming either digest below p. They do not
by themselves execute the enclosing caller or prove its return condition.
Build `C/jet_secp_generator_hash_literal.vo`, recursively kernel-check that
root, and compare its focused records, including the rebuilt unchanged
SHA/Bitcoin serialization dependencies. No public coverage row is added.
`jet_secp_generator_hash_map.exec_generator_hash_map` now composes the actual
SHA, conversion/return-flag update and SWU statements for either pass.
The computed digest and acceptance test are identified with the canonical
Simplicity hash expression. Rejected digests still execute the actual mapper;
the theorem derives their raw output too, without assuming successful
conversion. It preserves the key bytes, all six owned local objects,
framing, readonly state, both prefixes, and SHA/SWU startup, including the
mutable SHA dispatch cell. The existing `memcpy_model` and deferred ctz call
premise remain explicit; this is not a new accepted public theorem.
`jet_secp_generator_two_maps.exec_generator_two_maps` composes both passes
with the original intervening unblinded `gej_set_ge` call. It executes the
seven actual statements at generator indices 7--13 on the NULL-blinding
path selected by the public wrapper. Its output gives the first computed
point in the finite Jacobian accumulator with Z=1, the second computed
affine point, both coordinate bounds and canonical-SWU bridges on accepted
digests, and the exact conjunction of prior/conversion return flags.
It preserves all nine owned local objects, the key, framing, readonly
state and both startup families. No source, specification or digest-domain
restriction was added. Build `C/jet_secp_generator_two_maps.vo`, recursively
kernel-check `C.jet_secp_generator_two_maps`, and compare both modules'
focused assumption/contract records with the existing audit scripts.
`jet_secp_generator_begin.exec_generator_initial_prefix` executes all five
original FE_CONST limb stores, ret=1 and the initial NULL-blinding branch.
The closed RHS evaluation and actual uint64 stores are proved without an
initial value for the local field. Ownership, framing and readonly state
are derived from the stores. `jet_secp_generator_points_prefix` composes
this prefix with both hash-to-point passes: `exec_generator_points_prefix`
executes the first fourteen original statements and derives both points
and the exact conjunction of hash-conversion flags. It preserves the key,
all nine owned objects, framing, readonly state and both startup families.
The previous incoming-ret premise is discharged by the actual ret=1 assignment.
The existing memcpy/ctz premises remain explicit. Build
`C/jet_secp_generator_points_prefix.vo`, recursively kernel-check
`C.jet_secp_generator_points_prefix`, and compare both new modules' records.
Still missing: the enclosing canonical Simplicity hash-to-curve program's
branching/return connection; entry/allocation and final mixed addition,
affine/save and public load/write/return/free composition with global preservation.
The mixed-addition proof-interface gap is now discharged:
`jet_secp_mixed_function_loose.eval_mixed_function_xy` executes the entire
original NULL-rzr helper on the loose X/Y bounds produced by SWU, with all
ten allocations, original branches, result conversion and ten frees.
The preparation/difference/return/body/function proofs now share an explicit
X proof mode: the loose case retains the actual normalized U1, and the
positioned case specializes to the original unchanged helper contracts.
The equal-point/doubling branch uses the raw accumulator X/Y; the nonzero
branch uses normalized U1/S1. No tighter SWU bound, intermediate execution
or new external behavior is assumed. `mixed_function_readonly` is derived
from the original function's checked closed call graph.
`jet_secp_generator_add.exec_generator_add` executes the original generator's
statement 14 using that helper and derives its machine output coordinates,
flag, reusable bounds, ownership, framing, readonly and SHA/SWU/prefix startup
preservation. This span does not by itself compose the first fourteen
statements, prove the literal mixed-addition bridge for these loose inputs,
or complete the generator/public lifecycle. Build
`C/jet_secp_generator_add.vo` and the existing points-prefix target, recursively
kernel-check the addition root, and audit the six affected modules plus
rebuilt dependencies. Existing registered/legacy theorem and definition
records must still match exactly; coverage remains 514/533.
`jet_secp_mixed_xy_literal.eval_mixed_xy_literal` now connects the full original
mixed-addition helper on arbitrary matching loose coordinates to the complete
literal Simplicity expression. It reuses the general H/I residue tests and
nonzero arithmetic, retains raw-coordinate doubling, and covers the infinity
branch. There is no on-curve, canonical-input, nonzero-H, non-infinity-output,
libc or CTZ assumption. The input flag represents the initial Z zero test, as
in the existing reader theorem. `mixed_xy_affine_outputs_literal` specializes
the result to the generator's actual Z=1 initialization and decoded raw X/Y.
`jet_secp_generator_points_add.exec_generator_points_add` composes all first
fifteen original statements, including initialization, both SHA/SWU passes
and actual mixed addition. It executes every key; both digest acceptance
flags occur only in the postcondition identifying the canonical point sum,
not as restrictions on execution. It preserves the key, ownership of all caller
allocations, outside-block memory and SHA/SWU/prefix startup state. The existing
memcpy and deferred CTZ call premises remain explicit for the SHA/SWU prefix.
Build `C/jet_secp_generator_points_add.vo`, recursively kernel-check its root,
and run the existing focused assumption/contract audits for both new modules
and the reused prefix/addition dependencies. This closes the loose-coordinate
mixed-addition bridge and the first fifteen statements, not the generator's
affine/save/entry/return/free or whole-public caller. No new coverage is claimed;
the remaining suspected hash-to-curve infinity issue is not assumed away.
`jet_secp_generator_finish` now derives the original affine/save calls from
owned point fields for every machine infinity flag, then executes the actual
two tail statements and return. The saver adapter exposes both concrete
32-byte halves, retaining the original inspection and normalization calls.
`jet_secp_generator_sum_flag.generator_sum_flag_consistent` relates the
mixed-addition C flag to the canonical zero test of its decoded Z for the
actual initialized Z=1 input, including zero-H/doubling and infinity cases.
`jet_secp_generator_generate_body.exec_generator_generate_body` composes the
entire original NULL-blinding body, not a substituted program: initialization,
both SHA/SWU passes, addition, affine conversion, save and return. Every key
executes; the returned flag is exactly the conjunction of digest acceptance.
The postcondition identifies the canonical point sum on accepted digests,
the actual sum infinity flag, finite inverse/coordinate formulas or cleared
infinite coordinates, exact saved bytes, ownership, key/outside-memory framing
and preserved startup state. It retains explicit memcpy/CTZ premises.
The proof reuses the fourteen-statement prefix so its raw SWU bounds remain
available for the flag lemma; no previously recorded contract is weakened.
Build `C/jet_secp_generator_generate_body.vo`, recursively kernel-check its
root, and use the existing focused audits for the three new modules and their
reused execution/bridge dependencies. The then-missing entry/free and outer
generator call are now discharged below; the public lifecycle and final
canonical result/mismatch boundary remain open. Coverage stays 514/533.
An infinity-sum key is not assumed to exist or excluded.
`jet_secp_hashgen_entry.hashgen_entry` now constructs actual original function
entry with all eleven allocations, the exact parameter/temporary environment,
local ownership, distinctness/freshness, old-memory framing and readonly
preservation. `hashgen_blocks` checks the exact sorted freeing list.
`jet_secp_hashgen_function.eval_hashgen_internal` composes that entry, the
checked entire body, return conversion and all eleven original frees. The
audited `hashgen_result` retains the sum bounds, canonical correspondence on
accepted digests, actual infinity flag, exact saved bytes and finite/infinite
affine results. The call preserves the key, generator ownership, all other old
memory and SHA/SWU/prefix startup. No initialized output data is required.
`jet_secp_hashgen_outer.eval_hashgen_generate` then executes the original
outer `secp256k1_generator_generate`, including both pointer-check loops,
its NULL-blinding call, result conversion and return. The pointer checks are
proved from initial ownership/readability. The existing memcpy/CTZ premises
remain explicit; neither execution nor its desired output is assumed.
Build `C/jet_secp_hashgen_outer.vo`, recursively kernel-check that root, and
run focused assumption/contract checks for these three modules and the reused
body/tail/flag/prefix dependencies.
`jet_secp_hash_public_entry.hash_public_entry` now derives the public jet's
actual four allocations (16/32/64/88 bytes), fresh ownership and exact entry;
`hash_public_free` proves its exact four-object freeing list from ownership.
`jet_secp_hash_public_read.hash_public_prepare` executes the actual by-value
source-frame copy and raw `read8s` call at arbitrary valid cursors, including
word crossings. It derives all 32 key bytes, the advanced local cursor, retained
ownership and preservation of all caller memory. No output initialization or
field-range restriction is required. `hash_public_begin` in
`jet_secp_hash_public_generate` composes actual public entry, that prefix and
the original generator call, deriving its digest-acceptance return flag and
`hashgen_result` while retaining all four public locals and startup invariants.
The existing memcpy/CTZ premises remain explicit. Build and recursively
kernel-check `C.jet_secp_hash_public_generate`, then run the existing focused
audits for these three public-prefix modules.
`jet_secp_hash_public_finish.exec_hash_public_rest` now derives the public
failure/success branch, original load/write calls and actual return. Rejected
digests return zero without output writes; accepted digests write the saved
coordinates and return one, retaining the infinity case.
`jet_secp_hash_public_call.eval_hash_public_original` composes the entire
original public function, including actual entry, copy/read, generator call,
both branches, output writes, return conversion and all four frees. Its
`hash_public_value` retains the computed point bounds, literal mapped sum when
the digests accept, infinity flag and finite/infinite affine formulas after
the local storage is freed. It derives the output invariant and caller-memory
framing, at arbitrary valid frame cursors; it adds no input/output-disjointness
premise. Existing memcpy/CTZ premises remain explicit. Build and recursively
kernel-check `C.jet_secp_hash_public_call`, and run the existing focused audits
for these two final public modules. This is a complete C execution/result
characterization, not yet the canonical assertion equivalence or a public
divergence witness. The next obligation is that final specification connection,
including the possible infinity mismatch, without narrowing inputs. The raw reader uses
`vector_values (Word 3) 5 key`; do not substitute `read_fe`, whose normalization
would change keys at or above p before hashing.
The finite specification bridge now retains the already-proved numeric X/Y
equalities (`VX`/`VY`) from `eval_affine_finite_initialized` throughout
`eval_generator_affine_all`, affine/save/return, the complete generator body
and calls, and `hash_public_value` after the complete public call. These are
stronger postconditions; all previous conclusions and initial premises remain.
`jet_secp_hash_public_literal.hash_public_finite_literal` consumes that evidence
with `affine_normalized_words_literal` to identify the exact finite coordinate
pair with the fixed literal normalization program. Its
`literal_hash_to_curve_core` is the composition at Haskell lines 729--742,
reusing the checked SHA terms, canonical field modulus/comparison, SWU,
mixed addition and normalization. The comparison and program are parametric;
`hash_public_core_result` identifies the core specification result on every
key represented by `hash_public_value`, including digest rejection and the
infinity branch. The latter yields the core failure tag, while C's computed
return still depends only on the two digest acceptances. No actual common-key
infinity witness or impossibility theorem is established. Do not turn
the finite implication into a public input restriction. Build and recursively
kernel-check `C.jet_secp_hash_public_literal`, and audit the strengthened
generator/public contracts and their rebuilt consumers with the existing
focused tools.
`jet_secp_hash_to_curve_spec.literal_hash_to_curve` now includes the exact
outer Programs.Bit.assert with the existing canonical `assertion_cmr_fail0`.
Its parametricity and option-semantics proof connect the core failure tag to
assertion failure. `jet_secp_hash_to_curve_compare.eval_hash_to_curve_compared`
combines that exact specification with the complete original public C call,
its actual result/outputs/cursors and memory frame, for every represented key.
The checked `hash_public_return_agreement_iff` states that the computed return
agrees precisely when the digests reject or the sum flag is zero. In the
accepted-infinity case the C call succeeds and the assertion fails. Neither
that case's actual key reachability nor its impossibility is established;
there is no public counterexample or new coverage. Existing memcpy/CTZ
premises remain explicit. Rebuild and recursively kernel-check
`C.jet_secp_hash_to_curve_compare`, and use the existing focused audits for
these two modules. The assertion/caller composition is closed; leave the
reachability and deferred helper obligations open, and continue independent
jet families rather than replacing SHA or narrowing the public input.
These internal calls add no public coverage: 514/533 remains incomplete.
The serialization theorem alone does not identify registers with a computed
SHA digest, and neither these results nor their checked helper count add jet
coverage. Coverage remains 514/533.
Do not assume both digests are below p to avoid the rejection execution.

The sum-at-infinity branch also needs attention before a whole-public claim.
The canonical program can fail at `gej_normalize`, whereas the C return flag
only accumulates the two set_b32 results and generator_save's infinity check
is not a rejecting branch in the frozen AST. No actual input producing this
state has been exhibited. This is a source-review question, **not a proved
public mismatch**; exact evidence and limits are in
[JET_SECP_HASH_TO_CURVE_MISMATCHES.md](JET_SECP_HASH_TO_CURVE_MISMATCHES.md).
Do not add a non-infinity or hash-preimage restriction to the public theorem.

Reproduce the normal build with
`JET_TARGETS=C/jet_secp_generator_load_write.vo bash Coq/build-jets.sh -j2`,
recursive kernel check with `bash Coq/build-jets.sh --coqchk
-bytecode-compiler yes -silent -o C.jet_secp_generator_load_write`, and the
existing focused assumption/contract comparisons for these four modules.
For the saver, use `JET_TARGETS=C/jet_secp_generator_save_storage.vo` with the
same normal build, kernel-check `C.jet_secp_generator_save_storage`, and focus
the existing assumption/contract comparisons on the three new saver modules.
For the concrete round trip, build `C/jet_secp_generator_roundtrip.vo`,
kernel-check `C.jet_secp_generator_roundtrip`, and compare the existing
assumption/contract snapshots for `jet_secp_generator_save_initial`,
`jet_secp_generator_codec` and `jet_secp_generator_roundtrip`.

## Completed: `simplicity_gej_rescale`

`C.jet_secp_rescale_local.gej_rescale_literal_local_spec` now proves the
complete original public jet against the literal canonical Simplicity tree.
It covers unrestricted Word256 coordinates and scale (including zero), the
standard local-frame contract, actual reads and writes, return value and
local frees. No curve, nonzero, initialized-global or libc-model premise is
added. Its registration passed ordinary scoped acceptance, including all 291
kernel-checked dependency modules, reviewed assumption/contract comparisons,
negative tests and all five AST regenerations. Reproduce with
`bash Coq/check-jets.sh --accept --jets=simplicity_gej_rescale`.

The separate-output square support is now in the ordinary
`jet_secp_square_separate_{layout,exec,numeric,caller}.v` modules. It executes
the original helper into an uninitialized, distinct destination, preserves
the input and allocation permissions, and reuses the selected square proof's
arithmetic and literal-specification bridge. It is not a second registration
of `fe_square`.

`jet_secp_rescale_prefix.v` proves execution of the first two statements of
the actual helper body: the retained `fe_is_zero` check loop and the square
into local `zz`. The numeric endpoint preserves the scalar field, the point's
128-byte allocation permissions and `zz`'s 40-byte allocation permissions,
and supplies the square value and reusable limb bounds. There is no nonzero
scale premise. These are prefix/helper results, not a completed jet contract;
these prefix results alone did not increase coverage.

`jet_secp_rescale_entry.v` constructs the input representation from concrete
caller storage and proves actual function entry, parameter binding and fresh
`zz` allocation. `jet_secp_rescale_start.v` composes this with the prefix:
`rescale_start_from_storage` supplies the square result, reusable bounds,
preserved scalar and allocation permissions, all loads/permissions in the
original point block, and framing outside the caller's point/scalar blocks.
No initialized square destination or intermediate execution is assumed.

The `jet_secp_point_mul_{run,storage,numeric}.v` modules now execute actual
`fe_mul` calls at every point-coordinate offset while retaining ownership
of the whole 128-byte point. `eval_point_mul_numeric` derives execution,
the modular product, reusable bounds, source-field preservation and framing
from concrete caller storage. Its u128 event witnesses are discharged,
not caller premises. The shared `jet_secp_u128_word_*` and
`jet_secp_field_mul_word_*` modules adapt the archived independent helper
proofs, without registering alternative field jets. Their numeric model
uses the C routine's 56-/52-bit operand bounds: normalized-only 52-/48-bit
bounds would not follow from the square contract's 49-bit top-limb bound.

`jet_secp_point_mul_preservation.v` derives other-coordinate, flag and
third-block preservation. `jet_secp_rescale_calls.v` chains the four actual
callee executions; `jet_secp_rescale_statements.v` connects them to the four
original `Scall` nodes, using the existing generated-layout facts and proving
the local/global address evaluations. `jet_secp_rescale_owned.v` now proves
`eval_gej_rescale_owned`: actual entry, all six original body statements and
the final `zz` free, with exact output limbs, reusable bounds, unchanged
scalar/flag, retained caller ownership and external framing. This is the
complete **internal helper**, not the public jet-to-literal-specification
contract, and it does not increase registered coverage.

With the documented Coq 8.17.1 toolchain and matching pinned dependencies,
reproduce the focused build and recursive kernel check with:

```sh
JET_TARGETS=C/jet_secp_rescale_local.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_rescale_local
```

The kernel command enables the checker's supported VM conversion; it still
recursively checks every imported module, without admitting dependencies or
disabling kernel checks. The ordinary acceptance command remains unchanged.

`jet_secp_rescale_literal.v` ports the original Haskell `gej_rescale`, `zinv`
and cube trees. `rescale_reader_outputs_literal` connects all three helper
outputs through the existing wide field writer's value function to that
literal program for unrestricted Word256 inputs. It discharges the residue
premises from the normalized reader representation, including the difference
between C's two Y multiplications and the specification's cube expression.
This value bridge is composed with actual serialization by
`jet_secp_rescale_writer.v`, reusing `eval_write_gej_general`. The
`jet_secp_rescale_public_{entry,body,prepare,reads,call}.v` modules derive the
original three-local entry, source-frame copy, four reads, helper call,
writer call and frees. The final local endpoint uses the existing
`secp_jet_local_spec`, not a rescale-specific weakened contract.

The checked rescale closure uses the declared Coq 8.17.1 baseline (the Nix
compiler built with OCaml 4.14.4). The older reader/writer dependency closure
was rebuilt from source in a clean temporary tree under that baseline, then
the complete endpoint was rebuilt through the normal project target. No
compiler or dependency pin was changed to match older OCaml 4.14.1 caches.

`secp-field-integration/check-rescale.py` compares the actual catalog, GEJ/FE
types, Haskell rescale/cube/zinv trees, literal port and exact final contract;
12 targeted mutations are rejected. It supplements rather than replaces the
formal execution proof and is included in the ordinary acceptance command.

Coordinates live at offsets 0, 40 and 80 inside
one owned 128-byte point allocation. The existing owned multiply contract
requires each owned region's base to be zero; it cannot directly represent
a fictitious 40-byte allocation at offset 40 or 80. Reuse the whole-point
region pattern in `jet_secp_point_write_run.v` when extending execution
support. Claude's checked u128 helper oracles remain available in the
parallel-proof archive if needed; do not register the alternative
`fe_multiply` or `fe_square` endpoints as well as the selected ones.

## Completed proof: `simplicity_sha_256_block`

The complete C execution theorem in `jet_sha_block_local.v` and the
startup-invariant/preservation adapter in `jet_sha_startup_jets.v` are reused.
The older Coq SHA program uses `Word.adder` where Haskell uses `Arith.add`;
the bridge uses `canonical_add_word_matches_adder`, not syntactic identity.
The original compression proof is not repeated, and global-state scope
remains explicit below.

`jet_sha_block_literal.v` now has a shared block-tree template, a literal
`Arith.add word32 >>> ih` adapter, and a semantic equality to the older Coq
SHA program. `jet_sha_block_literal_local.v` composes that bridge with the
existing actual C execution theorem and the startup-state preservation
adapter; both local and persistent-startup contracts compile. The existing
SHA/startup dependency closure (including `sha_init_mem_exists`) was rebuilt
from source in a clean temporary tree under Coq 8.17.1/OCaml 4.14.4.

The literal constant-rotation and right-shift generators are now ported from
Haskell. Their SHA specializations equal the older Coq wiring in every Core
algebra, with closed program-equality proofs. The source-correspondence gate
compares the actual block Core trees, all 64 constants and reused word/bit
dependencies; 86 mutations exercise those checks and the exact public contracts.
This supplements, rather than replaces, the kernel-checked C proof.

The lifecycle endpoint derives dispatch from the existing caller lifecycle,
which starts at actual `Genv.init_mem` and preserves startup state through
owned memory operations and verified jet calls. Existence of this initial
memory/lifecycle is also imported and kernel-checked. The C dispatch pointer
is mutable: these results cover its initialized portable implementation,
not arbitrary externally installed optimized callbacks.

The registry selects the complete local contract with `sha_dispatch_ok`, not
the stronger startup/lifecycle preconditions. Ordinary scoped acceptance
passed the 264-module kernel closure, reviewed snapshots, negative tests and
all five AST regenerations. Reproduce it with
`bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block`.
The old C compression and reader/writer proofs are reused rather than reimplemented. Focused builds use
`JET_TARGETS=C/jet_sha_block_literal_local.vo bash Coq/build-jets.sh -j2`.
The candidate and actual initial-memory existence proof passed recursive
kernel checking with
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_sha_block_literal_local C.jet_sha_startup_init`.
The local endpoint inherits six assumptions and the stronger startup/lifecycle
endpoints eight, all within the existing Coq/CompCert allowlist. The two
startup/lifecycle variants are supporting results, not additional entries.

## Completed proofs: SHA context-add family

`jet_sha_ctx8_literal.v` connects the canonical block term under assertion/
option semantics, then the one-byte context-add program and the shared
sequential vector recursion. The actual one-byte C execution and startup
contracts compile in `jet_sha_ctx8_literal_local.v`; both retain `memcpy_model`
and their explicit SHA global-state requirements. No input counter, buffer
length or assertion-failure case is excluded.

The existing SHA source gate compares the one-byte Core tree, increment,
buffer-snoc/empty, count comparison and assertion-root dependencies, plus the
vector recursion and all ten catalog/type/contract specializations. Twenty
context mutations are rejected in addition to the block tests. All ten
complete local and startup contracts compile, reusing the shared bridge and
the existing C execution proofs. The ten registered local contracts all retain
`memcpy_model` explicitly; startup variants are not additional entries.
The family passed ordinary scoped acceptance: all 265 kernel-checked modules,
reviewed snapshots, negative tests and five AST regenerations, with unchanged
audited inputs and no expectation updates. The reproducible command is in
`JET_ACCEPTANCE.md`.
Focused builds use
`JET_TARGETS=C/jet_sha_ctx8_literal_local.vo bash Coq/build-jets.sh -j2`.

## Completed proofs: SHA buffer-add and finalization

The canonical buffer recursion is now in `jet_sha_buffer_literal.v`, reusing
the one-byte/vector/count bridges and retaining the empty-buffer assertion.
`jet_sha_finalize_literal{,_word}.v` ports the finalizer, all six padding
stages, buffer-size flags, count assertion/clearing, bit-length construction
and final block call. The constant left shifts and addition match the older
word programs in every Core algebra. Expose the old finalizer/padding wrapper
before conversion; do not normalize the large option program unnecessarily.

Both complete C execution and startup contracts compile in
`jet_sha_{buffer,finalize}_literal_local.v`, reusing the original execution
proofs without additional input restrictions. They retain `memcpy_model` and
their explicit global-state scope. The existing SHA source gate checks their
actual canonical trees and dependencies, with 24 additional rejected mutations.
The registry selects the two complete local contracts, with `memcpy_model`
explicit. Startup variants remain supporting results rather than additional
entries. The reproducible scoped acceptance command is in `JET_ACCEPTANCE.md`.
It passed all 276 kernel-checked dependency modules, reviewed snapshots,
negative tests and five AST regenerations, with unchanged audited inputs and
no expectation updates.

Focused builds use
`JET_TARGETS='C/jet_sha_buffer_literal_local.vo C/jet_sha_finalize_literal_local.vo' bash Coq/build-jets.sh -j2`.

## Completed: TapData registration and reusable simplification

`tapdata_init` reuses the complete C theorem in `jet_sha_tapdata_jet.v`, with
an explicit canonical program bridge. Its scribed prefix is computed from
the actual `Digest.tagIv`/`ivHash` recipe, not an unexplained numeral.

The shared bridges now use a closed improvement:
`@canonical_add_word (S n) term = @Word.adder (S n) term` is reflexive in every
Core algebra. In particular `@literal_sha_add32 term = @SHA256.add32 term`
is reflexive, and rewriting it in `literal_sha_256_block` followed by
`sha_block_tree_existing` gives a closed equality in every Core algebra.
These stronger bridges are now in ordinary sources and remove unnecessary
functional-extensionality dependencies from the option bridges, without
changing any target or public C theorem type.

`jet_tapdata_host_recipe.v` ports the fixed two-block recipe from the actual
vendored `Digest/Pure/SHA.hs`, using unsigned Word32 operations. Closed Coq
computations establish the tag bytes, padding, complete block lengths, tag
digest and prefix. This is not a claimed arbitrary Haskell decoder interpreter.
`jet_tapdata_literal{,_local}.v` composes the canonical initializer with the
existing complete C and startup contracts; both compile with their original
explicit libc/global/tag requirements. The existing SHA gate compares the
recipe, all 64 rounds and 48 schedule steps, encoding and exact C contracts;
131 mutations are rejected. The registry now selects this endpoint. Ordinary
scoped acceptance passed for it and all thirteen affected SHA endpoints:
281 recursive kernel modules, 176 assumption modules, 189 contract modules,
negative tests and all five AST regenerations, with unchanged audited inputs.
The command and exact scope are recorded in `JET_ACCEPTANCE.md`.

## Completed: Bitcoin pure builders and context hashes

`jet_bitcoin_taproot_literal{,_local}.v` now reuses the existing original C
proofs for `bitcoin_build_tapleaf_simplicity` and `bitcoin_build_tapbranch`.
Both complete local and startup-preserving contracts compile, retaining
`memcpy_model` and the existing SHA/tag-state premises. The ten canonical
program/constant bridge lemmas are closed. These compose the actual C execution
and full framing conclusions, without a transaction-environment/cache premise.

These modules reuse the fixed host SHA structure for the two tag prefixes and
`haskell_hash_word256` for byte/hash-to-word conversion. The source gate compares
the complete canonical trees, relative vector-size dispatch, shift/order/padding
wiring and final C boundaries, including actual library-instance projections,
rejecting 27 additional mutations. The host recipe review concerns these two
fixed tags, not arbitrary Haskell decoders.

`jet_bitcoin_ctx_hash_literal{,_local}.v` similarly composes the original
outpoint/annex C proofs with the checked literal context-add programs. The
option bridges cover every counter and both optional-input branches, retaining
the complete success/failure contract, `memcpy_model` and SHA readiness.
Local and startup variants compile and passed recursive kernel checking with
supported VM conversion; both bridge lemmas are closed. Width-specific rewrites
avoid unfolding symbolic SHA computations. The source checker follows the
actual Bitcoin library bindings and complete assertion trees, rejecting 14
further mutations. The registry selects all four endpoints. Ordinary scoped
acceptance passed: 292 recursive kernel modules, 186 assumption modules,
200 contract modules, negative tests and all five AST regenerations, with
unchanged audited inputs and no expectation updates. The reproducible command
and remaining scope limits are recorded in `JET_ACCEPTANCE.md`.

## Completed: primitive-bearing SHA bridges and Bitcoin tappath hash

The context-add, buffer-add and finalizer now have closed equality variants
for every assertion algebra, in addition to their unchanged option interfaces.
Existing program definitions and public C theorem types are unchanged. The
proofs reuse `literal_sha_256_block_core_matches` and structural induction;
no new semantic assumption or functional-extensionality premise is needed.

`jet_sha_hash_words_literal.v` composes these bridges into the canonical
initializer, bounded/early-stopping `hashLoop` and `hashWord256s` structures.
`jet_bitcoin_tappath_hash_literal.v` instantiates the program with the existing
Tappath primitive and composes the original complete C getter proof. The exact
`hash_getter_rep ... 8 40 176` relation, frame separation and formal environment
are retained. This is a cached-field jet: cache establishment by a caller is
not proved by the new theorem. No extra libc premise is added.

All ten new program bridges are closed; the C theorem inherits six library
assumptions. Normal builds, recursive kernel checking with supported VM
conversion, and reviewed comparisons of the five affected snapshot modules
passed. The source checker follows the actual SigHash library instances,
initialization, traversal/termination, 8-bit indexing and selected primitive,
and rejects 25 further mutations. Host interpreter correspondence is
source-reviewed, not a general Haskell interpreter correctness theorem.

The existing extended environment restricts paths to 128 entries, matching the
well-formedness guard in the real C taproot builder; no domain is changed here.
The other inherited Bitcoin-domain discrepancies remain documented in
`JET_BITCOIN_MODEL_MISMATCHES.md`. The registry selects the new tappath-hash
endpoint. Ordinary expanded acceptance passed for it and fourteen affected
consumers: 315 kernel-checked modules, 194 assumption comparisons, 211 contract
comparisons, global source/mutation checks, negative tests and all five AST
regenerations. Audited inputs stayed unchanged; no expectations were updated.
Reproduce with the scoped command in `JET_ACCEPTANCE.md`.

## Completed: Bitcoin script and sequence array hashes

`jet_bitcoin_array_hash_literal.v` composes the shared literal SHA initializer,
early-stopping traversal and finalizer with four original C getter proofs:
output scripts, input scripts, input sequences and input scriptSigs. One closed
program equality works for every indexed primitive and primitive algebra; the
four adapters select the canonical 32-bit index and 32-byte/4-byte elements.
No C implementation, prior execution proof or formal domain is changed.

The endpoints retain `application_jet_local_spec_sep` and the existing
`hash_getter_rep` relations (transaction offsets 48, 176, 240 and 304), with no
additional libc premise. They prove the cached getters, not caller cache
construction or unrestricted Haskell-environment representability. In
particular, the frozen transaction-domain boundaries in
`JET_BITCOIN_MODEL_MISMATCHES.md` remain unresolved; the two extended script-hash
lists are still represented abstract environment fields, not newly established
raw-script projections.

All four endpoints compile in the normal project. Reviewed assumption and
contract snapshots match: the general program equality is closed, and the C
theorems each inherit six library assumptions. The existing SHA source checker
also checks the four full canonical programs, library dispatch, selected
primitive projections, widths and whole public contracts, rejecting 34 further
mutations. These host projections are source-reviewed, not a general Haskell
interpreter theorem. Recursive kernel checking with supported VM conversion
passed, with no assumptions outside the inherited allowlist and no unsafe
kernel features. The four endpoints are selected in the registry. Ordinary
scoped acceptance passed: 241 kernel-checked modules, 126 assumption
comparisons, 143 contract comparisons, global source/mutation checks, negative
tests and all five AST regenerations. Audited inputs stayed unchanged and no
expectations were updated. Reproduce with the command in `JET_ACCEPTANCE.md`.

## Completed: raw interpretation of five composed Bitcoin programs

`jet_bitcoin_raw_program.v` restores the generic bridge from the preserved
`proof-work/bitcoin-raw-program` source, unchanged. It relates every parametric
program to the existing raw interpretation, including both assertions and
failure. `jet_bitcoin_hash_raw_literal.v` composes it with the accepted literal
array/tappath endpoints: all five complete C contracts now also have variants
interpreted on raw script/scriptSig/taproot data. This ties extended script-hash
primitive inputs to raw bytes without changing the primitive signature or
frozen base domain. The original abstract-environment endpoints are retained.

Both modules compile in the normal project under the fixed Coq 8.17.1
toolchain. Reviewed assumption and contract records match. The primitive
projection and two literal-parametricity lemmas are closed; the general
program-relation/projection lemmas inherit functional extensionality, and the
C endpoints retain the same six inherited library assumptions. No additional
libc, execution or desired-output premise is added. The existing source checker
protects the raw interpretation, representation boundary and five full C
contracts, rejecting 22 further mutations. The registry selects these five raw
variants with no coverage-count change. Ordinary scoped acceptance passed:
272 kernel-checked modules, 143 assumption comparisons, 166 contract comparisons,
global source/mutation checks, gate negative tests and all five AST regenerations.
Audited inputs stayed unchanged and no expectations were updated. Its
reproducible command is in `JET_ACCEPTANCE.md`.

This does not prove cache construction by the C environment builders, remove
the existing path bound in `raw_env_rep`, or repair the reported Bitcoin-domain
mismatches. The archived concrete endpoints and their old README remain
historical, not current acceptance evidence.

## Completed: canonical tapleaf/tap-environment getters

`jet_bitcoin_tap_hash_literal.v` adapts the preserved tapleaf combinator tree
to the accepted fixed-tag host recipe and algebra-general SHA bridges. It adds
literal `tapleafHash` and `tapEnvHash` programs, exact program equalities for
every primitive algebra, and complete original-C getter contracts in both the
abstract and raw interpretations. The tagged-context adapter is general over
a supplied prefix; the host tag computation is the already-checked fixed
`TapLeaf` recipe, not a new arbitrary-tag interpreter claim.

The existing `bitcoin_tapleaf_hash_local_spec` and
`bitcoin_tap_env_hash_local_spec` executions are composed, not assumed at the
final boundaries. The cache relations remain `hash_getter_rep ... 8 8 176`
and `hash_getter_rep ... 8 72 176`, lifted through `raw_env_rep` for the raw
endpoints. Caller cache construction, the existing path bound and the reported
Bitcoin-domain differences remain separate obligations.

The module compiles under the fixed Coq 8.17.1 baseline; older unregistered
dependency objects were rebuilt from source. Reviewed assumption and contract
records match: all five program/parametricity lemmas are closed, and the four C
variants retain six inherited library assumptions without an extra libc or
execution/output premise. The existing source checker compares both canonical
Core trees with the actual explicit algebra applications, tagged initialization,
primitive/raw projections and all four complete C boundaries. It rejects 22
further mutations. The registry selects the two raw endpoints. Ordinary scoped
acceptance passed with 282 kernel-checked modules, matching assumption records
for 153 modules and contract records for 176 modules, negative tests and all
five AST regenerations. Its command is in `JET_ACCEPTANCE.md`.

## Completed: canonical input outpoints, annexes and combined-input hashes

`jet_bitcoin_inputs_hash_literal.v` supplies literal programs for
`inputOutpointsHash`, `inputAnnexesHash` and `inputsHash`, reusing the original
generic element-loop body and the accepted literal SHA/context programs.
The outpoint and annex append equalities are generalized to every assertion
algebra without changing the existing option-only APIs. The shared element
adapter and all three program equalities/parametricity bridges are closed.

Six complete original-C getter contracts compose the existing executions with
these bridges, in both abstract and raw primitive interpretations. Their cache
relations remain `hash_getter_rep ... 0 <offset> 432` at offsets 112, 272 and
336, respectively. There is no new libc, execution or output premise; all six
contracts retain the same six inherited library assumptions. Caller cache
construction, the raw path bound and the frozen-domain differences remain
separate obligations.

The normal project build passes under the pinned toolchain, after rebuilding
unchanged stale dependencies from source. The existing source checker compares
the complete canonical loop/composition trees, primitive interpretations and
all six C boundaries and rejects 33 further mutations. In particular, an
absent input stops the annex loop, whereas a present input without an annex
continues and appends a zero byte. Reviewed snapshots cover all fifteen public
theorem types/assumption sets and the four new program definitions; comparison
without update flags passes. The registry selects the three raw endpoints.
Ordinary scoped acceptance passed with 280 kernel-checked modules, matching
assumption records for 151 modules and contract records for 174 modules,
negative tests and all five AST regenerations. Its command is in
`JET_ACCEPTANCE.md`.

## Completed: canonical computing single-input hash

`jet_bitcoin_input_hash_literal.v` composes the existing complete original
`input_hash` execution with a literal canonical program over primitives. The
three bridges are closed; the two C variants retain the same six inherited
library assumptions and the explicit `memcpy_model` premise. The registry
selects the raw variant; ordinary scoped acceptance passed.

Unlike the cached composite getters, this C function computes SHA over the
selected input's outpoint, sequence and optional annex. Its existing
`input_hash_rep` relation, including SHA-global readiness and environment/output
separation, is retained. It covers the original absent-input, absent-annex and
present-annex branches; caller construction/startup and frozen-domain limits
are not discharged. The source checker compares the whole canonical assertion
tree and both complete conditional C boundaries, rejecting 27 further mutations.

## Completed: canonical Elements array hashes

The preserved `jet_sha_hash_words_reader.v` and
`jet_elements_words_hash_program.v` are restored without source changes into
the normal build. They reuse the existing SHA traversal, context absorption and
finalization proofs over an arbitrary option Reader, then instantiate the actual
Elements primitive algebra and complete original C cache getters. There is no
artificial Bitcoin environment or assumed hash/execution oracle.

`jet_elements_array_hash_literal.v` connects seven getters to the shared literal
SHA programs: output scripts/range proofs/surjection proofs, input scripts/
sequences/scriptSigs, and tappath. Both generic bridges are closed. The seven
complete C contracts retain the same six inherited assumptions and no extra
libc premise. Their represented cache values come from raw logical script/proof
bytes, unsigned sequences or taproot paths. Cache construction by actual callers,
the existing path/domain bounds and general host-library fidelity remain open.

The source checker compares canonical dispatch, array widths/counters, raw
primitive/proof views and all seven C boundaries, rejecting 51 further mutations.
Both candidate families compile in the normal pinned-toolchain build after
rebuilding unchanged stale dependencies. Reviewed snapshots cover 50 public
theorem records and 20 definitions across the four modules; comparisons without
update flags match all four. The registry selects the eight final endpoints;
ordinary scoped acceptance passed, with its command in `JET_ACCEPTANCE.md`.

## Completed: Elements input and taproot hash getters

Six preserved modules are restored unchanged into the normal build: the
generic option-Reader element loop, Elements annex/outpoint/combined-input
programs, and Elements tapleaf/tap-environment programs. The outpoint loop
retains both primitive lookups and both early exits. There is no new assumed
hash or execution oracle, nor an artificial Bitcoin environment.

`jet_elements_inputs_hash_literal.v` connects three complete original C getters
to literal canonical programs. Nine bridges are closed; the three C contracts
retain the same six inherited assumptions and no extra libc premise. Their
`hash_getter_rep` offsets are 216, 376 and 440 in the 760-byte transaction.

`jet_elements_tap_hash_literal.v` connects two complete original C getters to
the canonical tapleaf/tap-environment programs. Seven bridges, including the
fixed `"TapLeaf/elements"` host recipe, are closed. Both C contracts retain
the same six inherited assumptions and no extra libc premise, at offsets 8
and 72 in the 176-byte taproot environment. Native `Schnorr.PubKey` carries
`Word256`; this adapter does not assume that arbitrary words are valid curve
points or field elements.

Normal compilation and the existing complete source checker pass. The new
checks reject 36 input-tree/boundary mutations and 32 taproot/tag/key/boundary
mutations, including whitespace changes inside the tag. Reviewed snapshots
cover 55 theorem records and 32 definitions across the eight modules.
Caller/cache construction, the existing domain/path bounds, and general
host-library fidelity remain separate obligations. These five endpoints are
selected in the registry; ordinary scoped acceptance passed, with its
command in `JET_ACCEPTANCE.md`.

## Completed: Elements issuance-proof, nonce and amount hash getters

Six preserved support modules are restored unchanged, reusing the generic
option-Reader element loop, prefix/payload absorber and complete original C
getters. Three new adapters target the canonical primitive-bearing programs:

- `jet_elements_issuance_proofs_hash_literal.v`: both issuance-proof primitive
  lookups and early exits, with the existing closed asset/token proof-view
  lemmas reused for absent issuance, reissuance and explicit/confidential cases.
- `jet_elements_nonces_hash_literal.v`: absent output stops, whereas a present
  output without a nonce absorbs byte zero. Explicit nonce words use prefix 1;
  confidential native words use prefix 2 or 3. The existing native Word256
  encoder bridge is reused, not replaced by a field-element restriction.
- `jet_elements_amounts_hash_literal.v`: shared asset, amount and asset/amount
  serializers serve input and output hash loops. Confidential assets use
  prefixes 10/11, confidential amounts 8/9, and explicit values prefix 1.
  Explicit amounts retain their 8-byte payload; the other payloads are 32 bytes.

All four complete C endpoints retain the original `hash_getter_rep` relation,
at transaction offsets 536, 56, 24 and 248 in the 760-byte structure. They have
the same six inherited library assumptions and no extra libc premise. The 17
adapter bridges are closed. Normal compilation passes after rebuilding unchanged
stale dependencies under the pinned toolchain. The existing source checker
rejects 19, 20 and 26 further mutations; reviewed snapshots cover 65 theorem
records and 52 definitions across the nine modules.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. These four endpoints
are selected in the registry; ordinary scoped acceptance passed, with its
command in `JET_ACCEPTANCE.md`.

## Completed: Elements composite hashes, blinding entropy and issuance status

Ten preserved support modules are restored without source changes; two new
adapters connect the complete C getters to the shared literal programs.
`jet_elements_composite_hash_literal.v` uses one fixed-vector SHA skeleton for
the four-component output hash and two-component input-UTXO hash.
`jet_elements_blinding_entropy_literal.v` retains all three primitive lookups,
the optional/new/reissuance routing and the actual `Arith.one word8` program,
not a substituted constant. Its padding dependencies are compared with the
canonical Haskell program. Eight adapter bridges are closed. The three complete
C contracts keep the original cache relations at transaction offsets 184, 312
and 568 in the 760-byte structure.

The preserved `jet_elements_issuance_status_local.v` is already a literal
primitive-program endpoint for the original `simplicity_issuance`. It covers
out-of-range input, no issuance, new issuance (false), and reissuance (true).
Its initial relation represents only pointers/count and the enum at input
offset 528, with stride 544 and count offset 696. It has no cached-hash,
execution, desired-output, nonzero-issuance or initialized-output premise.
The actual enum reload after the first payload write is preserved by the
derived write effect. The local preservation contract still requires valid
separated frames; it is not an overlapping-buffer API claim or caller-builder
proof.

All four C endpoints retain the same six inherited library assumptions and no
extra libc premise. Normal compilation passes after rebuilding unchanged stale
dependencies with the pinned toolchain. Source checks reject 26 composite,
24 blinding-entropy and 17 issuance-status mutations, including reversed
`flip match` branches and vacuous final contracts. Reviewed snapshots cover
55 theorem records and 43 definitions across twelve modules.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. These four endpoints
are selected in the registry; ordinary scoped acceptance passed, with its
command in `JET_ACCEPTANCE.md`.

## Candidates: Elements computed issuance getters

`jet_elements_issuance_computed_literal.v` now composes the complete original
entropy/asset/token getters with literal primitive-bearing programs, sharing
one C getter proof and the existing universal SHA/word bridges. Every Word32
index and issuance-kind branch is retained. The initial canonical cache
relation remains a caller obligation, not an assumed execution or final output.
Normal compilation, source checks and ordinary scoped acceptance pass; the
reviewed snapshots and acceptance command are described in `JET_ACCEPTANCE.md`.
These three endpoints are registered local contracts.

## Candidate: Elements annex context hashing

`jet_elements_annex_context_literal.v` now composes the original context jet
with the shared literal annex program and existing nonce/SHA frame contract.
The normal build and source checks pass, including assertion-failure cases.
It retains explicit SHA-global and `memcpy_model` premises and passed ordinary
scoped acceptance together with the computed issuance getters. See
`JET_ACCEPTANCE.md` for scope and the command.

## Completed local contracts: Elements taproot builders

Both whole original C builder calls now compile in
`jet_elements_tap_builders_literal.v`. The Elements-specific tagged-context,
hash-I/O and comparison execution modules reuse the existing SHA and nonce
frame infrastructure. Literal adapters share the accepted tapleaf payload,
universal SHA bridge and fixed host tag recipe. Their initialized frame
contracts retain `memcpy_model`, SHA dispatch/counter and actual tag-byte
premises. Both endpoints passed ordinary scoped acceptance, including all
309 kernel dependency modules. The scope and reproducible command are in
`JET_ACCEPTANCE.md`.

## Completed local contracts: Elements issuance amount and composite hashes

`jet_elements_issuance_amounts_hash_literal.v` now compiles the complete C
`issuance_asset_amounts_hash` and `issuance_token_amounts_hash` getters against
primitive-bearing literal traversals. Both reuse the existing element loop
and asset/amount serializer, with a shared two-null-byte absent-issuance
adapter. `jet_elements_issuances_hash_literal.v` composes them with the
accepted range-proof and blinding-entropy programs, retaining the latter's
actual `one word8` program, and proves the original composite C getter.

Normal compilation and full source correspondence pass (40 further mutations
rejected). The public C endpoints use only the six inherited assumptions and
no extra libc premise. Initial cached-hash correspondence, represented
environment/frame admissibility and general caller construction remain
explicit obligations. All three endpoints passed ordinary scoped acceptance,
including all 392 kernel dependency modules. See `JET_ACCEPTANCE.md` for scope
and the reproducible command.

## Candidates: Elements transaction and signature hashes

`jet_elements_tx_hash_literal.v` and `jet_elements_sig_all_hash_literal.v`
now compile the complete original getters against their full literal,
primitive-bearing programs. They reuse the component-hash theorems and
byte-list absorption/finalization lemmas, rather than repeating SHA execution.
The transaction hash keeps the version/locktime prefix, canonical order of
four component hashes and final input-UTXO hash. The signature hash keeps both
copies of GenesisBlockHash, transaction/tap-environment hashes and CurrentIndex.

The shared `jet_elements_direct_hash_getter.v` proves the direct txEnv-field
wrapper needed by the latter, with the same complete application-frame
contract and existing `writeHash` execution. The former retains the existing
pointer-field getter framework. Their initial canonical cache relations at
transaction offset 632 and txEnv offset 48 remain caller obligations. No
execution/output premise or extra libc model is introduced. Normal builds,
source correspondence and 26 targeted mutations pass. Both entries passed
ordinary scoped acceptance (406 kernel modules, 274 assumption modules, 299
contract modules, negative tests and five regenerated ASTs). Accepted local
coverage is 491/533. See `JET_ACCEPTANCE.md` for scope and the command.

The remaining indexed computing Elements hash jets need actual C helper
execution, not just cache-getter registration. `input_utxo_hash` is the smallest
next representative: read index/tag, initialize SHA, execute confAsset/confAmt
and hash calls, finalize, serialize and free, including the out-of-range branch.
The ordinary C tree now contains live-context execution proofs for the actual
jet translation unit, adapted from the archived Elements-environment call
structure without identifying the two programs:

- `jet_elements_confidential_exec.v`, `jet_elements_confidential_wrap.v` and
  `jet_elements_conf_amount_exec.v`: actual confidential/asset/nonce/amount
  helper calls over `ctxi`, with exact counter/overflow transitions and memory
  effects. The absent confidential case does not require initialized payload
  words; explicit amounts retain their full 64-bit range.
- `jet_elements_conf_hash_bridge.v`: closed byte-stream bridges to the existing
  asset/amount Simplicity serializers. `jet_elements_conf_hash_repr.v` connects
  their existing memory representations to actual helper execution. The C
  results retain `memcpy_model` and the six inherited library assumptions.
- `jet_elements_input_utxo_hash_spec.v`: the primitive-bearing composition and
  its raw-environment semantics, including the out-of-range result. Its
  parametricity proof is closed; its semantics uses inherited functional
  extensionality. This is support, not a whole-jet C theorem.

These six support modules compile in the normal project; reviewed snapshots
cover 37 theorems and 14 definitions and compare without update flags. They do
not add a registration or claim whole-jet acceptance.

The complete candidate is now in `jet_elements_input_utxo_{prep,payload}.v` and
`jet_elements_input_utxo_hash_{jet,literal}.v`. Its final theorem
`elements_input_utxo_hash_literal_local_spec` proves the actual C call against
the primitive-bearing literal program, including both index branches, context
initialization, actual helper calls, finalization, serialization and frees.
It retains arbitrary valid frame cursors, unknown old output contents, prefix
and cursor preservation and external framing. The initial relation describes
the actual input-array asset, amount and script-hash fields, plus SHA readiness;
no intermediate execution or desired final digest is assumed. The payload uses
the general streaming lemma, including 74/98-byte compression-boundary crossings.

Normal builds and canonical source-tree checks pass; 24 new targeted mutations
are rejected. Reviewed snapshots cover 23 theorems and eight definitions in
these four modules and compare without update flags. The literal bridges are
closed; the C endpoint retains the six inherited assumptions and explicit
`memcpy_model`. Ordinary scoped acceptance passed, including kernel checking of
428 modules and all five AST regenerations; accepted local-contract coverage is
492/533. Raw-environment establishment, startup/caller
admissibility and libc implementation linkage remain distinct obligations.
Bitcoin domain blockers and Elements fee questions remain separate. Check
`JET_CLAIMS.md` before starting another jet.

## Completed local contract: computing Elements output hash

`jet_elements_output_hash_{spec,prep,payload,jet,literal}.v` and
`jet_elements_nonce_hash_repr.v` now compile in the normal project. The final
`elements_output_hash_literal_local_spec` covers the actual whole C call and
canonical primitive-bearing program, not merely the serializer or digest math.
It reuses the indexed-frame/private-local spine and streaming SHA bridge from
input UTXO hashing; its extra nonce/script/range-proof calls are proved in order
with memory preservation. Absent nonce payload words need not be initialized.

Reviewed snapshots cover 22 theorems and 12 definitions. Literal bridges are
closed; the C endpoint retains six inherited assumptions and `memcpy_model`.
The source checker rejects 30 targeted mutations. Ordinary scoped acceptance
passed, including kernel checking of 444 modules and all five AST regenerations;
accepted local-contract coverage is 493/533. Caller, environment-cache, libc and
evaluator obligations are unchanged.
Check `JET_CLAIMS.md` before starting another jet.

## Completed local contract: computing Elements input hash

Six support modules provide the four-primitive program/literal bridge,
all-index semantics, actual optional-hash and u32 SHA calls, complete digest
payload chain, optional statement adapters and entry/body/pointer lemmas.
Their reviewed snapshots cover 24 theorems and 16 definitions.

The new `jet_elements_single_input_jet.v` reuses the input UTXO frame/init/
writeHash/free spine and proves the actual whole C function. The final
`elements_single_input_hash_literal_local_spec` is in
`jet_elements_single_input_literal_jet.v`. Both new modules compile normally;
reviewed snapshots cover two theorems and two initial representation definitions.

The initial relation uses stride 544, annexHash 0, pegin 32, prevOutpoint 96
(txid 96 and ix 128), sequence 248, hasAnnex 536 and isPegin 537, without the
UTXO offset 136. It requires optional payloads only when present and SHA readiness.
The intermediate loads, calls, digest and frame/return/free facts are proved
from that relation, not assumed. All valid cursors and old output contents remain
covered. Literal bridges are closed; the C endpoint retains the six inherited
assumptions plus `memcpy_model`. The source checker rejects 34 new mutations.
Ordinary scoped acceptance passed, including kernel checking of 434 modules and
all five AST regenerations. Accepted local-contract coverage is 494/533.
Check `JET_CLAIMS.md` before starting another jet.
Builder/caller, libc and evaluator obligations remain separate.

Old cached u32be and environment-call objects were rebuilt from unchanged source
under the baseline toolchain; no version pins or production sources changed.

## Computing Elements issuance_hash: accepted whole C proof

The seven foundational modules compile normally: `jet_elements_single_issuance_{spec,literal,
prep}.v`, `jet_elements_issuance_{asset_literal,zero_literal,zero_array}.v` and
`jet_elements_indexed_flag.v`. Reviewed snapshots cover 30 theorems and 25
definitions. The canonical all-index semantic/literal bridge reuses the accepted
issuance calculations, optional asset/amount serializer and actual one8 blinding
program. The general payload bound is 261 bytes; the absent-issuance message is
69 bytes. The whole endpoint described below compiles and is registered;
ordinary scoped acceptance has passed.

The C support proves both real confidential-ID literals (typed struct copy plus
explicit prefix), the reissuance explicit-zero amount and the new-issuance
32-byte zero initializer from arbitrary writable memory. Closed AST equalities
match these initializers. Do not assume their contents in the final theorem.

Use the flag-parameterized indexed wrapper: this function stores writeBit's
result in t'3 and uses t'2 as an amount pointer. The old t'2 wrapper is not its
body. `eis_entry`, `eis_body`, `eis_blocks` and `eis_copy` cover eight locals,
allocated in order/sizes: src 16, midstate 32, ctx 88, compound 36, compound1 36,
compound2 40, compound3 32, __res 88. Derive ownership/freshness from those real
allocations and use `eis_blocks`'s actual free-list order.

`jet_elements_single_issuance_none.v` now proves execution of the actual
no-issuance branch and its finalize call, with digest words equal to the
canonical 69-byte payload hash and preservation outside the private SHA
context/midstate. Its premises require only the two proof hashes, not inactive
issuance fields. It compiles in the normal build; its theorem/definition and
inherited-assumption snapshots are checked. It is branch support, not a whole
jet acceptance result.

`jet_elements_single_issuance_asset.v` composes construction and absorption
of both actual asset/token ID prefixes. `exec_eis_id_hash` selects either real
subtree, derives its source expression from `_issuance`, and establishes the
corresponding canonical explicit-asset bytes in the running SHA context. It
checks assetId/tokenId offsets 168/200 against the frozen composite environment.
Private-object separation and writability must be discharged from `eis_entry`'s
allocations by the eventual whole-function proof, not imposed on callers.

`jet_elements_single_issuance_amount.v` proves the actual asset amount call and
the complete token amount selection/absorption for both active kinds. The new
path derives the nested-union address at offset 32; the reissuance path executes
the local zero initializer and requires no inactive tokenAmt representation.
`eis_token_le` records the actual updates to t'6/t'2. Their compiled contracts
preserve the running SHA state and frame loads outside the private objects.

`jet_elements_single_issuance_{blinding,tail}.v` now execute both actual
blinding branches and the shared proof-hash/present-marker suffix. The new
path establishes and absorbs all 32 zero bytes; the reissuance path loads only
the active nonce/entropy fields. The byte bridge uses the canonical 256-bit
zero word, and the common suffix absorbs exactly 129 bytes. Context, load,
permission and validity preservation are included in these compiled contracts.

`jet_elements_single_issuance_active.v` completes both actual active payload
branches and finalization in `exec_eis_some_finalize`. It executes all four
ID/amount prefixes and the suffix, and proves equality of the final digest words
to `sha256_bytes_of (eis_some_message ...)`, whose bytes are the canonical
`elements_single_issuance_bytes`. No execution or desired result is a premise.
Together with `exec_eis_none_finalize`, all three payload cases now compile.
These remain internal branch results, not a complete or registered C jet.

`jet_elements_single_issuance_{rep,dispatch}.v` now provides that initial
representation by issuance kind, the canonical message bridges, its bounded
load-preservation lemma, and `exec_eis_dispatch_finalize` for the actual outer
type test plus all three payloads/finalization. `eis_payload_le_dst` preserves
the destination temporary. The relation's asset/token caches are tied to the
existing primitive-based issuance calculations, not the desired final digest.

`jet_elements_single_issuance_{jet,literal_jet}.v` now compiles that whole
function. `elements_single_issuance_hash_literal_local_spec` proves the original
`f_simplicity_issuance_hash` against the literal primitive-bearing program,
conditional on `memcpy_model`, initial field/cache correspondence and SHA
readiness. The proof discharges private freshness/writability from all eight
actual allocations and includes source-frame copying, both index branches,
issuance address setup, SHA init/copy, type dispatch, payloads, writeHash, return,
the actual free-list and framing. It covers arbitrary valid frame cursors and
existing output bits. No payload execution or desired digest is a premise.
The ordinary build and reviewed contract/assumption checks pass. The endpoint
is registered and passed ordinary scoped acceptance.

The existing source checker now compares the whole canonical `issuanceHash`
Core tree, full literal C boundary and every initial-field/cache definition;
50 additional mutations are rejected. The exact contract is guarded in coverage,
the single endpoint is registered, the memcpy conditional count is 136, and the
claim is removed. Reproduce ordinary scoped acceptance without update flags:
`bash Coq/check-jets.sh --accept --jets=simplicity_issuance_hash`.
Acceptance passed build, kernel checking, reviewed assumption/contract snapshots,
gate negative tests and all five regenerated ASTs. Accepted local-contract
coverage is 495/533; the whole every-jet goal remains unfinished.
The element's issuance starts at offset 256; checked
existing fields include entropy 72, proof hashes 104/136, assetAmt 232 and type
272. The ID offsets 168/200 and union tokenAmt offset 32 are checked against
the AST. Extend the existing canonical-tree/full-contract source check
and run ordinary acceptance only after the final whole-C literal endpoint.
Caller/cache establishment, libc and evaluator obligations remain separate.

## Accepted: ge_is_on_curve

The main session claims `simplicity_ge_is_on_curve` in `JET_CLAIMS.md`.
Twenty-two ordinary modules now compile: internal support and the complete
registered public curve endpoint. Ordinary scoped acceptance has passed:

- `jet_secp_field_add7.v`: actual `fe_add_int(7)`, exact field-value increment,
  no-wrap bounds, owned storage and framing for loose multiplication outputs.
- `jet_secp_curve_weak{,_math}.v`: actual weak normalization from five limbs
  bounded by `2^60`, exact output loads, modular-value preservation, lower
  52-bit limbs and top limb at most 281474976710912, ownership and framing.
- `jet_secp_curve_zero{,_math}.v`: actual `fe_normalizes_to_zero_var`, including
  its fast return; its bit accumulators detect zero modulo the field prime.
- `jet_secp_curve_equal.v`: actual `fe_equal_var`, including allocation/freeing
  of its private temporary, returns equality modulo the field prime for lower
  52-bit/top 49-bit operands and preserves both input representations/framing.
- `jet_secp_curve_mul.v`: actual in-place multiplication of a 40-byte temporary
  by X inside an 88-byte affine input, with proved event witnesses, source
  preservation and tight 52-/49-bit product bounds. It reuses `point_mul_table`,
  `fm_solves`, and the existing field arithmetic, not a second public endpoint.
- `jet_secp_curve_square{,_caller}.v`: selected original optimized C square
  from either affine X (offset 0) or Y (offset 40) into a separate, possibly
  uninitialized 40-byte temporary; output/source loads, caller ownership,
  modular square value, tight bounds and framing are proved.
- `jet_secp_curve_frame.v` and `jet_secp_curve_calls.v`: reusable enclosing-object
  and disjoint-field framing, plus `curve_square_cube_calls`, which composes
  the actual Y-square, X-square and in-place cube calls in C order. It derives
  both modular values, tight bounds, source-field preservation and ownership
  across all three memories; neither temporary needs initialization.
- `jet_secp_curve_tail{,_values}.v` and `curve_six_arithmetic_calls` now compose
  all six actual arithmetic calls in C order. The returned C integer is exactly
  the comparison of Y² with X³+7 modulo the field prime, derived from the initial
  limbs. Both private temporaries and the affine input remain Freeable; input
  fields and external framing are preserved. This arithmetic-call composition
  is used by the containing Clight function below, not substituted for a literal jet.
- `jet_secp_curve_statements.v`, `jet_secp_curve_body.v` and
  `jet_secp_curve_function.v`: `eval_curve_finite_function` proves the whole
  original `f_secp256k1_ge_is_valid_var` for a finite affine object. It establishes
  both actual 40-byte allocations and freshness, binds the actual parameter,
  executes the flag load/finite branch and all six arithmetic statements,
  converts the return integer and frees both private objects in the actual
  `blocks_of_env` order. Its preconditions contain no intermediate execution,
  final result, private buffer or allocation premise. X/Y, source ownership and
  external framing are preserved. The flag-zero premise must be derived from
  the actual affine reader in the public jet proof, not imposed on jet inputs.
- `jet_secp_curve_literal{,_bridge}.v`: the full literal canonical projective
  and affine Core trees, their parametricity, and `eval_curve_finite_literal`.
  The latter connects the complete original helper to the literal affine bit
  for every pair of Word256 inputs represented by the actual reader's limbs.
  Reader reduction modulo P preserves the comparison; no canonical-input or
  on-curve premise is added. It retains the derived-reader obligations (X/Y
  fields, finite flag and owned 88-byte object), not a public frame contract.
  The residue lemmas are closed; the literal numeric bridge inherits functional
  extensionality and the execution theorem retains the same six library
  assumptions. Both ordinary modules and reviewed snapshots pass.
- `jet_secp_curve_public_{body,rest,call}.v` and `jet_secp_curve_local.v`:
  `ge_is_on_curve_literal_local_spec` now compiles as the whole original public
  `secp_jet_local_spec`, not a helper-only theorem. The proof derives both public
  allocations, the by-value source-frame copy, the real affine reader's fields
  and zero flag, the full validity-helper call, the bit write, successful return
  and actual public local frees. No intermediate execution, initialized output,
  canonical input or on-curve premise is imposed on its public contract.
  The ordinary target `JET_TARGETS=C/jet_secp_curve_local.vo bash Coq/build-jets.sh -j2`
  passes; all four reviewed contract/assumption snapshots match without update
  flags. The endpoint retains the same six inherited library assumptions and
  needs no extra libc premise. Its single exact endpoint is registered and
  has passed ordinary scoped acceptance.

These are C execution-plus-value contracts, not just relations between jet
specifications. The helper integer bridges are closed; execution contracts retain
only the six inherited library assumptions. No extra libc model is needed.

The existing `check-secp-predicates-specification.py` source gate now checks
the full projective/affine curve trees, catalog dispatch/implementation, shared
cube/one ports and the exact public endpoint contract. Its mutation suite rejects
62 variants (28 new curve cases). Other field ports retain their existing gates.
`jet-coverage.py` also enforces the exact boundary and its negative tests pass.
Only `C.jet_secp_curve_local.ge_is_on_curve_literal_local_spec` is registered;
the claim is removed. On `ad63ab2b`,
`bash Coq/check-jets.sh --accept --jets=simplicity_ge_is_on_curve` passed build,
kernel checking of all 341 dependency modules, 280 assumption and 295 contract
records, gate negative tests and all five regenerated ASTs, with unchanged
audit inputs. Accepted coverage is 496/533: 360 without an extra libc premise
and 136 conditional on `memcpy_model`. The full every-jet goal is not complete.
The numeric `curve_result` alone is not the jet specification. The
Haskell target is `ge_is_on_curve = iden &&& (unit >>> fe_one) >>> gej_is_on_curve`;
its local `fe_cube = iden &&& fe_square >>> fe_multiply` must be retained in the
literal port. Do not replace it by an assumed numeric curve equation. Add source-fidelity
checks and scoped acceptance only after that whole endpoint compiles.

Cached square dependencies had inconsistent assumptions over
`jet_canonical_add_adapter`. The affected unchanged sources were rebuilt under
the Coq 8.17.1 baseline, first in temporary output and then in the normal build;
both selected public field endpoints also recompiled. Do not change toolchain
pins or mix OCaml objects. The old affine reader/lifecycle objects also needed
rebuilding from their unchanged sources under the baseline (OCaml 4.14.1 caches
were incompatible with 4.14.4); both the temporary and normal rebuilds passed.
Square certificate comparisons are split by fixed
input offset and limb, retaining the 10-second command bound.
Claude's alternative public field endpoints remain unregistered; do not merge
`dd4579a7` or duplicate the selected `fe_multiply`/`fe_square` rows.

## Completed: gej_x_equiv

The main session completed `simplicity_gej_x_equiv`; its claim is removed.
`C.jet_secp_x_equiv_local.gej_x_equiv_literal_local_spec` retains the original
total public contract: unrestricted `(FE, GEJ)` words, including zero Z and
the real infinity short-circuit. It adds no finite-point, on-curve, initialized
output, intermediate execution or libc-model premise. The ordinary build,
reviewed snapshots and recursive kernel check pass. Ordinary scoped acceptance
also passed on `0b694db8`: 318 kernel modules, 257 assumption modules, 272 contract
modules, gate negative tests and all five regenerated ASTs, with unchanged inputs.

`jet_secp_point_square_z.v` now proves the actual optimized square from offset
80 of an owned 128-byte point into an uninitialized distinct 40-byte temporary.
`eval_point_square_z_from_storage` supplies the modular square, reusable limb
bounds, source Z loads, both Freeable ranges and external framing;
`point_square_z_foot` bounds the conservative footprint to the output and the
source Z cells. It reuses the selected square arithmetic through five closed
expression equalities. The ordinary build, reviewed snapshots and recursive
kernel check pass; this is support, not a registered new jet. For the recursive
check use the same stack limit as `check-jets.sh`:

```sh
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_point_square_z
```

`jet_secp_x_equiv_literal.v` supplies the full literal `gej_x_equiv` target,
including the infinity guard and the negation/addition/zero-test tree. Its
parametricity and semantic-step lemmas are closed; the numeric comparison
bridge inherits only functional extensionality. The ordinary build and reviewed
contract/assumption comparisons pass. This module does not prove C execution
and is not a coverage registration. Keep this literal tree as the target,
rather than replacing it by the numeric equation.

`jet_secp_field_pair_multiply.v` now adapts the selected original C multiplier
to two owned 40-byte fields with loose 56-/52-bit input bounds. It derives the
actual call, modular product, tight 52-/49-bit output bounds, source preservation,
both ownership ranges and framing. The in-place output initially contains the
first input; in X-equivalence this input comes from the actual Z square. There
is no separate zero-initialization or desired-result premise. The normal build,
reviewed contract/assumption comparisons and recursive kernel check pass. No
fresh oracle or alternate multiplier is introduced; no additional jet is registered.

`jet_secp_x_equiv_copy.v` proves the original by-copy `r2 = a.x` assignment,
including the typed field loads and ownership after the real byte copy.
`jet_secp_x_equiv_tail.v` composes the original weak-normalize and equality
calls. The product must retain the multiplier's tight output bounds: the
looser `square_input_bounds` alone do not meet the comparison precondition.
Both modules pass the normal build, reviewed contract/assumption comparisons
and recursive kernel check with the six inherited library assumptions. These
are helper results, not additional public-jet equivalence registrations.

`jet_secp_x_equiv_prefix.v` composes the actual Z square and in-place multiply
while preserving the caller's point allocation and X argument. The exact
original helper statement tree, retained no-op loop and call/address derivations
are in `jet_secp_x_equiv_statements.v`. `exec_x_equiv_body_owned` in
`jet_secp_x_equiv_body.v` derives the complete original body from these storage
contracts: no intermediate call execution, copied field or desired result is
assumed. It includes the return statement, but not function entry or private
frees. All three ordinary modules build, their reviewed snapshots match, and
the body with its recursive dependencies passes the kernel check. These body
milestones alone did not establish the complete public contract.

`eval_x_equiv_function` in `jet_secp_x_equiv_function.v` now proves the entire
original `secp256k1_gej_eq_x_var` call: two real local allocations, parameter
binding, body, return conversion and both frees. Its premises are caller-owned
point/field storage, separation and the reader-compatible loose limb bounds;
no intermediate allocation, execution or desired result is assumed. The
ordinary build, reviewed contract/assumption comparisons and recursive kernel
check pass. The helper works for zero Z as well; it does not assume a finite
or on-curve point. Its numeric result alone is not the guarded public jet theorem.

The `jet_secp_x_equiv_public_{reads,statements,rest,lifecycle,call}.v` modules
connect the literal target and real public wrapper. The original
`simplicity_gej_x_equiv` reads the separate field first, then the point: input
order is `(q,((x,y),z))`, not the rescale reader's `(x,y,z,s)` order. Its local
allocation order is source frame (16), separate field (40), point (128). They reuse
`eval_read_fe_with_cursor_capacity` followed by `eval_read_gej_canonical_fields` at
`rc+256`, preserving the already-read field across the point reader, and keep
the one-bit output contract (`1 <= N`), not rescale's 768-bit requirement.
The public infinity flag is derived by `read_gej`; its true branch skips the
arithmetic helper and returns the false bit. Both branches, the actual bit
writer, all allocations, the by-value source-frame copy and public frees are
derived. Only the whole literal-equivalence endpoint is registered.

The existing predicate source gate now checks this catalog binding, full
Haskell/Coq literal routing, infinity dependency, Bit.and port and exact public
contract. Its 87 mutations include 25 new X-equivalence/dependency cases.
The registry checker also enforces the exact direct endpoint. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_x_equiv
```

The capacity-parametric cursor reader in `jet_secp_read_fe_cursor_capacity.v`
now derives the actual field read and advanced cursor for any nonnegative
output capacity fitting N. The older `eval_read_fe_with_cursor` fixes capacity
256 and must not be used to strengthen this jet's one-bit output premise.
`jet_secp_x_equiv_literal_bridge.v` proves the reader-product residue and the
guarded helper-result equality to the full literal target, including zero Z.
These two ordinary modules pass build, reviewed contract/assumption comparisons
and the recursive kernel check. They add no jet coverage.

Do not infer full input ownership from a borrowed view: `foot` conservatively
includes read cells, and `rw=false` alone does not retain a whole Freeable
object. Keep the actual enclosing allocation in the execution contract.

## Completed: gej_is_on_curve

The main session completed `simplicity_gej_is_on_curve`; its claim is removed.
Its literal program,
semantic-step lemma and parametricity proof live in
`jet_secp_curve_literal.v`. The whole original public function is now proved
against that literal program in
`C.jet_secp_gej_curve_local.gej_is_on_curve_literal_local_spec`.
The public contract admits arbitrary Word256
X/Y/Z values and one output bit, not only genuine or finite curve points.

The actual helper is `f_simplicity_gej_is_valid_var`, defined in
`C/jets-secp256k1.c`, not libsecp's affine validity checker. It deliberately
tests the polynomial `y^2 = x^3 + 7*z^6` without checking the infinity flag, and
accepts `(0,0,0)` as the canonical infinity representative. Do not import the
affine helper's early infinity rejection into this proof.

The ordinary build now includes the following reusable proof chain:

- `jet_secp_point_square_coordinate.v` squares X/Y/Z at offsets 0/40/80,
  retaining ownership of the full 128-byte point. It reuses the selected
  square proofs instead of deriving new arithmetic.
- `jet_secp_field_point_multiply.v` derives the actual reverse-direction
  call: private temporary multiplied in place by a point coordinate.
  It reuses the selected multiplication log and output lemmas.
- `jet_secp_square_inplace_storage.v`, `jet_secp_field_mul7.v`,
  `jet_secp_field_add_scaled.v` and `jet_secp_equal_loose.v` cover the
  remaining calls, with exact limbs, derived bounds and memory frames.
- `jet_secp_gej_curve_{coordinate,prefix,tail,calls}.v` composes all nine
  arithmetic calls in original C order; there are no assumed intermediate
  call executions or desired outputs in `gej_curve_arithmetic_calls`.
- `jet_secp_gej_curve_statements.v` identifies the unchanged original body.
  `jet_secp_gej_curve_function.v` derives that body from owned storage,
  allocates and frees its three temporaries, and proves the bool return
  conversion in `eval_gej_curve_function`.
- `jet_secp_gej_curve_literal_{numeric,bridge}.v` relates the helper to the
  existing literal program for all three input words.
  `eval_gej_curve_literal` accepts the actual canonical reader limbs and
  full point ownership; it has no infinity-flag premise.

Unlike the affine checker and X-equivalence, this C helper does not
weak-normalize the sum before equality. The new comparison proof handles the
derived loose second operand without inserting a normalization call.

The `jet_secp_gej_curve_public_{statements,rest,call}.v` modules compose
`eval_read_gej_canonical_fields` with capacity 1, `eval_gej_curve_literal`,
the actual boolean-typed bit writer and the owned 128-byte point/public frame
lifecycle. The public `_t'1` has type `tbool`, unlike the infinity/affine
predicate wrappers' `tint`; its exact generated statement is retained.
No finite/infinity-flag premise is added. The standard local-contract endpoint
is registered, the existing predicate fidelity gate is extended, and scoped
acceptance passed on `408a485c` (321 kernel modules, 260 assumption modules,
275 contract modules, negative tests and all five ASTs). Accepted coverage is
498/533; 35 declarations remain. Reproduce the public result with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_is_on_curve
```

To reproduce the internal-helper build and recursive kernel check with the
baseline Coq 8.17.1 on PATH and prepared jet dependencies:

```sh
JET_TARGETS=C/jet_secp_gej_curve_literal_bridge.vo bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_curve_literal_bridge
```

## Completed: gej_double

The public endpoint is registered and passed ordinary scoped acceptance on
`23b1ca34`; the main session's next claim is `simplicity_gej_ge_add`.
`jet_secp_double_literal.v` ports the canonical
`gej_double` pairing/projection tree, `fe_halve` (including its one-bit shift),
and `fe_multiplyInt`; its routing and parametricity lemmas are closed. These
are specification bridges, not additional C-jet coverage. The completed proof
executes the actual `secp256k1_gej_double_var` caller with `rzr = NULL`, its
early infinity branch and the in-place `secp256k1_gej_double` arithmetic.
Keep arbitrary coordinates, including Y=0, when reusing it;
do not restrict to genuine curve points. Equivalence helpers call point
addition, so they are not independent shortcuts around this work. Normalization
and Y-parity also need the uncompleted inversion proof.

Reuse the selected square/multiply arithmetic, the coordinate storage/frame
adapters above, `eval_read_gej_canonical_fields`, and the general bounded point
writer (`eval_write_gej_general`, with `rescale_point_field`/bounds adapters).
The first memory obligation, `r.z = a.z * a.y` with `r = a`, is now proved by
`eval_point_zy_mul_owned`: both sources and the destination inhabit one actual
128-byte allocation. `jet_secp_owned_slice_fields.v` combines/extracts slices
of that owned region; do not pretend they are separate allocations. The reverse
square layout (private L into point X) is now proved by `eval_square_point_x`:
precise framing restores the full point allocation and preserves Y/Z/flag
bytes. `eval_point_y_product` now proves the later Y destination multiplication
from two private fields, reusing the selected u128 log and numeric lemmas.
Its three-allocation initial representation follows from full point ownership
and the two actual operand fields; initial Y contents need not be defined.

The actual `secp256k1_fe_half` execution is now proved in
`jet_secp_field_half.v`, without an input-limb bound needed for execution.
`jet_secp_field_half_numeric.v` derives reusable loose output bounds and
`2 * radix_value output = radix_value input + low_bit(input) * feP` under
the established loose input bounds. The shared `jet_secp_field_mul_small.v`
handles signed C multipliers from zero through seven on tight limbs.
`eval_double_l_scale` composes the real multiply-by-three and halve calls,
preserving ownership, external memory, the resulting value identity and bounds.
All these modules build normally and pass focused assumption/contract and
recursive kernel checks; execution results retain only the same six inherited
assumptions, with no added libc-model premise.

`double_prefix_calls` now derives the first five arithmetic calls from initial
storage. `eval_negate_sep_from_storage` proves the next actual negation into
uninitialized T, preserving S and deriving the exact value `4*feP - value S`
and reusable bounds. `double_middle_calls` composes that negation, multiplication
by the initial X, and the square of L into X. `double_front_calls` composes all
eight calls from the initial point and three owned temporaries, with no
intermediate execution/output premises. It returns the actual `square_words L`
at X and `double_t_words initial_X S` at T, along with S, L, unchanged Y,
updated Z and all ownership permissions.

The shared `eval_point_field_add` now proves original C addition for every
point coordinate and both argument orders, retaining the full 128-byte point
allocation and a precise frame for the other coordinates. Its machine-output
contract needs no arithmetic range premise. `jet_secp_field_sum_bounds.v`
derives no-wrap facts, exact radix sums and reusable scaled limb bounds from
the preceding tight outputs; these are caller facts, not new domain constraints.
`double_accumulate_calls` composes calls nine through twelve (X += T twice,
S = S^2, T += X). `double_first_twelve_calls` then derives all twelve calls from
the initial storage. It preserves Y/Z and L, returns the updated X/T/S machine
fields, full ownership, and bounds for the last three calls.

`eval_point_y_negate2` proves the actual magnitude-two, in-place negation at
offset 40, deriving the exact value `6*feP - value Y` and reusable output bounds
from the preceding sum's bounds. `double_y_tail_calls` composes all three final
calls. `double_all_arithmetic_calls` now derives all fifteen original helper
calls, output fields, full point/temporary ownership and writer bounds from the
initial point and three owned temporaries. No intermediate execution/output
premise is required.

`double_helper_source` identifies the original generated body exactly as the
flag load/store followed by `double_arithmetic_body`.
`exec_double_arithmetic_owned` executes that actual arithmetic suffix from
owned storage, discharging every call premise internally. The subsequent
`double_flag_copy_owned` derives preservation of all three coordinate fields
and permissions from the real Mint32 flag store. `exec_double_body_owned`
executes the complete original body. `eval_double_function` composes both
parameter bindings, the three actual allocations, that body, the void result
and all frees. Allocation order is L/S/T; the checked `blocks_of_env` free
order is S/L/T. It accepts arbitrary bounded coordinates and any integer flag.

`eval_point_normalizes_zero` reuses the checked variable-time zero-test
arithmetic on any owned point coordinate, including loose limbs and the early
return. The final result is zero modulo the field prime, not merely a test of
canonical limbs. Do not substitute `fe_is_zero` for this actual C helper.

`jet_secp_double_var_statements.v` proves the original NULL-rzr dispatch
statements for both branches. `eval_double_var_owned` now composes the entire
original `secp256k1_gej_double_var` function, with both point parameters aliased
and the actual 64-bit NULL value for `rzr`. Its finite branch derives the
arithmetic outputs, Z-zero test and final flag store; its incoming-infinity
branch reuses the real initializer and returns zero coordinates. All field
preservation, flag-store existence, ownership and external-memory framing are
derived internally. There is no on-curve or nonzero-coordinate hypothesis and
no intermediate call/output premise in that theorem.

These internal execution/output results alone do not establish public jet
equivalence; the public composition below is required. Reproduce the normal
helper build and recursive kernel check with the baseline toolchain and
dependencies described above; focused assumption/contract audits use the
existing scripts and each module's reviewed snapshots:

```sh
JET_TARGETS=C/jet_secp_double_var_owned.vo bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_double_var_owned
```

The arithmetic-to-literal bridge is now derived, not assumed:

- `jet_secp_double_half_literal_numeric.v` observes the actual literal shift
  and conditional-add tree. For every word its result is canonical, and twice
  that result equals the input modulo p. The width-generic bit-vector value
  adapters reuse the existing shift proof; no new shift executor is needed.
  Literal small-integer multiplication is also related to its numeric value.
- `jet_secp_double_half_bridge.v` combines that result with the actual C half
  identity, including loose input limbs and multiply-three/half composition.
- `double_body_coordinates_match` in `jet_secp_double_coordinate_numeric.v`
  derives all three arithmetic-output residues against the literal body,
  deriving every needed intermediate limb bound. Its hypotheses are only
  initial bounds and input/specification residue agreement, not curve or
  nonzero-coordinate assumptions.
- `double_reader_outputs_literal` relates the actual reader-derived words and
  flag, through the output decoder, to the complete literal program. It handles
  both incoming infinity and finite inputs. `eval_double_var_literal` composes
  that equality with the checked real C function, deriving its output fields,
  writer bounds, ownership and external-memory frame.
- `eval_write_gej_doubled_literal` composes the existing general point writer
  with those fields and output equality. It proves actual XYZ serialization
  and the resulting encoded literal value in `finv`.

The public wrapper is now composed in `jet_secp_double_public_{boundary,rest,call}.v`:
the actual source-frame copy and two local allocations, canonical point reader
with capacity 768, real doubling helper, unconditional XYZ writer, true return
and both frees. It reuses the checked point-jet lifecycle and
`rescale_reader_limbs` rather than adding post-call framing/ownership premises.
`jet_secp_double_local.v:gej_double_literal_local_spec` is the complete standard
`secp_jet_local_spec` for the original public function against
`literal_gej_double`, over every Word256 triple and the normal valid frame
contract. Compilation and the reviewed focused assumption/contract audits pass;
the endpoint retains the same six inherited execution assumptions and no added
libc, curve-membership or nonzero-coordinate premise.

The existing point-program correspondence check
`secp-field-integration/check-rescale.py` now also freezes the doubling catalog,
literal half/integer-multiplier/doubling trees and full public theorem. It
rejects 27 targeted doubling mutations; the existing full-shift and inherited
field gates retain responsibility for those dependencies. The coverage test
also rejects vacuous, wrong-function and weakened doubling registrations.
The registered endpoint passed the full scoped check on `23b1ca34`: 355 kernel
modules, 294 assumption modules, 309 contract modules, negative tests and all
five regenerated ASTs. Accepted coverage is 499/533, with 34 remaining.
Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_double
```

Follow the writer body, which writes X/Y/Z unconditionally: an infinity flag
alone does not imply all-zero stored coordinates. In particular, retain the
finite-input Y=0 case; its final infinity flag can be true while the stored
X/Y are nonzero. The input-infinity branch explicitly sets all coordinates to
zero. These cases are included in the accepted theorem.

## Completed: gej_ge_add

The main session completed `simplicity_gej_ge_add`, the original mixed
projective/affine addition jet. It reuses the accepted doubling helper for its
equal-point branch and the selected multiply/square infrastructure. The
public affine reader establishes a zero infinity flag for B; derive that
fact from the reader rather than adding a public input restriction.
`jet_secp_field_copy_owned.v` proves the actual struct assignment into an
uninitialized, distinct field slice, deriving the copied words, permission
preservation and precise framing from readable source/writable destination
storage. It uses CompCert's struct-copy rule, not a libc-model premise.
`jet_secp_point_set_bit.v` proves the actual `fe_set_int(0/1)` on any coordinate
slice inside one owned 128-byte point. It handles the generated assertion loop
without changing assertion settings or treating the slices as separate blocks.
`jet_secp_gej_set_ge_owned.v` composes the flag store, both field copies, actual
Z initializer, entry and return of the original affine-to-projective helper.
`jet_secp_mixed_head.v:mixed_infinite_body_owned` executes the actual mixed-add
body's incoming-infinity branch, retained loop, NULL-rzr test, helper call and
early return. It derives the resulting fields, zero infinity flag, ownership
and external frame from storage; no intermediate call/output is assumed.
These internal results do not register another jet. The finite branch still
needs its full arithmetic, zero tests, literal-program bridge, public
reads/writes, entry and frees.

`jet_secp_add_literal.v` ports the canonical `gej_add_ex`, `gej_add`,
`gej_ge_add_ex` and `gej_ge_add` trees, including both infinity branches,
the zero-H/equal-point distinction and the original ratio output. The ports
are algebra-parametric; do not replace them with an arithmetic formula.
`jet_secp_mixed_infinite_literal.v:mixed_infinite_body_literal` composes the
actual incoming-infinity branch with the reader-word and actual writer-value
bridges. Its infinity case hypothesis selects this internal branch, not a
restriction on a registered public jet. It derives all output fields, writer
bounds, literal output equality and framing without an intermediate call or
desired-result premise. Public writer execution and the finite branch remain
to be composed.

The existing `secp-field-integration/check-rescale.py` also compares these four
literal ports with the fixed Haskell routing and rejects 13 targeted addition
mutations. This source-correspondence check supplements the formal proofs;
it does not establish whole-jet addition execution or register coverage.

`jet_secp_mixed_finite_start.v:exec_mixed_finite_start` now derives execution
of both finite infinity-flag checks and the first actual square, `z12 = a.z^2`.
`mixed_finite_source` identifies these statements inside the original generated
body. The square contract supplies actual output words, modular value, reusable
bounds, input preservation and full point/local ownership. This is a prefix,
not the complete function. The composed preparation is below; H/I and their
zero tests remain. Reuse the checked weak
normalization and reader-identity results (`jet_secp_curve_weak{,_math}.v`,
`jet_secp_point_weak_values.v`) instead of repeating their arithmetic.

`jet_secp_field_weak_tight.v:eval_field_weak_tight` now derives the actual
private-field weak-normalization call and exact unchanged output words for
positioned limbs, reusing those checked execution/carry identities.
`square_reader_positioned` discharges the limb bounds for every reader input.
`jet_secp_mixed_copy_weak.v:exec_mixed_copy_weak` derives both actual U1/S1
struct-copy and weak-normalization statements from storage, with uninitialized
destinations, full allocation permissions and unchanged source point. Its
`mixed_copies_source` identifies both pairs inside the original body, separated
by the actual U2 multiplication. No intermediate execution or desired output
is a premise. Their preparation-path composition is below; the remaining
finite arithmetic is still required before a whole-jet contract can be registered.

`jet_secp_mixed_affine_product.v:eval_mixed_affine_product` now derives the
actual `fe_mul` into an uninitialized private field from either coordinate of
the actual 88-byte affine object and a separate private operand. It reuses the
selected multiplication/u128 log and proofs, deriving the output words,
modular product, reusable bounds, all three allocation permissions and precise
framing for the other affine coordinate/flag. `exec_mixed_affine_call` connects
it to both actual U2/initial-S2 `Scall` nodes; `mixed_affine_calls_source`
identifies their positions. No desired execution/result or fresh-word oracle
is assumed.

`jet_secp_mixed_s2_calls.v:exec_mixed_s2_calls` composes both consecutive
original S2 multiplications, `S2 = B.Y * z12; S2 *= A.Z`. It derives the exact
result words, triple-product residue, reusable bounds, preserved source fields,
full point/affine/temporary ownership and precise framing from initial storage.
No intermediate execution/result is assumed.

`jet_secp_mixed_preparation.v:exec_mixed_finite_preparation` now composes the
entire finite preparation path from initial storage: both infinity checks,
the square into uninitialized z12, U1/S1 copies and weak normalizations, U2,
and both S2 multiplications in original order. It derives all prepared words,
reusable bounds, preserved input fields/zero flags, allocation permissions and
the precise external frame. The seven named storage blocks are distinct
(`NoDup`), as the actual caller's fresh allocations will establish; no
intermediate execution/output or initialized-temporary premise is added.
`mixed_finite_preparation_source` identifies the original generated statement
spine exactly. The existing `statement_sequence` prefix combinator, including
its final proof-only `Sskip`, attaches the remaining original suffix; it does
not skip any C statement. `exec_mixed_preparation_then_rest` demonstrates that
composition for the after-square portion. The H/I stage is below; zero-test
branches, final arithmetic, literal-value bridge and public lifecycle remain.
This internal prefix does not register additional jet coverage.

`jet_secp_field_sum_owned.v:eval_field_sum_owned` reuses the actual private
addition execution and exposes the unchanged source words as well as the
destination sum and both allocations' permissions. It has no arithmetic
range premise. `jet_secp_mixed_difference.v:exec_mixed_differences` now
composes the four actual H/I statements from prepared private storage:
negate U1 into H, add U2, negate S2 into I, add S1. It derives the exact
words, `4*p - minus + plus` values, loose reusable bounds, all preserved
source fields and six owned temporaries, without execution/output premises
or initialized H/I destinations. The same pair proof handles H and I;
source equalities retain the generated statement order.

`jet_secp_mixed_finite_prefix.v:exec_mixed_finite_difference` connects the
complete finite preparation to those four H/I statements. It derives the
tight H/I operand bounds from positioned-reader bounds and the existing
`double_mul_tight`/`double_tight_loose` results, and carries initially
uninitialized H/I storage through preparation using its memory frame. The
result preserves all point/affine inputs and both flags, returns the exact
U/S/z12/H/I words, nine owned allocations and the combined frame. Its source
equality identifies the whole original body prefix through H/I; no execution,
intermediate output or tight multiplication-result premise is assumed.
These are internal execution results, not a new public jet registration.

`jet_secp_field_zero_owned.v:eval_field_zero_owned` adapts the existing
`eval_curve_zero_numeric` to actual owned 40-byte fields; it derives the
zero-mod-p return, unchanged words and retained ownership from initial
storage. `jet_secp_mixed_zero.v` uses this for the actual H and I call nodes
and proves the nonzero-H guard falls through. The H=0 branch body is proved
in `jet_secp_mixed_zero_branch.v`: `exec_mixed_equal_branch` tests I and
executes the real in-place `gej_double_var` when I=0;
`exec_mixed_inverse_branch` tests I, skips the NULL-rzr write, executes the
real infinity initializer and returns when I is nonzero. Both derive their
calls from storage and preserve I ownership/words and an external frame.
The equal branch retains the actual doubling coordinates, even when the
resulting infinity flag is set; it does not silently zero those coordinates.
`jet_secp_mixed_zero_return.v:exec_mixed_zero_return` now derives the H test
and both I-dependent early returns as one execution of
`mixed_after_difference`, preserving H/I ownership and words. It covers
either I result, rather than assuming an intermediate branch execution.
`jet_secp_mixed_finite_return.v:exec_mixed_finite_zero_body` attaches this to
the checked finite preparation: the complete original helper body executes
from initial point/affine fields and uninitialized private storage when its
computed H is zero modulo p. It derives its H/I storage and bounds, returns
the actual conditional coordinates/flag, all nine named allocations' ownership
and an external frame. This is an internal branch theorem: finite flags and
H=0 select this path; they are not restrictions on a registered public jet.
`jet_secp_mixed_nonzero_start.v:exec_mixed_nonzero_prefix` now derives the H
test and the first four nonzero-H statements from initial owned fields:
clear the infinity flag, skip the NULL-rzr copy, multiply the actual point Z
by H, and square H into an uninitialized H2. It reuses
`double_var_store_flag`, `eval_point_mul_numeric` and
`eval_square_separate_from_storage`; X/Y, H, ownership and precise external
framing are preserved. The Z product and H square values/bounds are returned.
`mixed_nonzero_prefix_source` identifies this exact prefix of the original
remaining body.

`jet_secp_field_negate_owned.v:eval_inplace_negate_tight_owned` adapts the
already-checked original in-place negation to tight limbs (including a 49-bit
top limb), with no new execution model. `jet_secp_field_product_owned.v`
proves the original multiplication into an uninitialized private destination
from two distinct private inputs, reusing the selected u128 execution
oracles, event witnesses and multiplication arithmetic. No libc premise is
introduced. `jet_secp_mixed_products.v:exec_mixed_products` derives the actual
H2 negation, H3=H2*H and T=U1*H2 statements from owned fields.
`jet_secp_mixed_nonzero_products.v:exec_mixed_nonzero_products` connects these
to the H test, flag store, NULL-rzr skip, Z update and H square. It derives
all intermediate bounds, preserves X/Y, H and U1 and returns exact Z/H2/H3/T
words, six owned allocations, product bounds/residues and a precise frame.
It does not assume initialized H2/H3/T contents or intermediate executions.
`jet_secp_mixed_x_tail.v:exec_mixed_x_tail` derives the actual five statements
X=I^2, X+=H3, X+=T twice, T+=X from owned fields; X need not be initialized.
It preserves I/H3, ownership and the point's untouched slices, and derives
scaled bounds 4 for X and 5 for the updated T with exact radix values.
`jet_secp_mixed_y_tail.v:exec_mixed_y_tail` derives the final Y=T*I, H3*=S1,
Y+=H3 calls, using the original point-Y and in-place private multiplication
proofs. `exec_mixed_xy_tail` composes all eight X/Y statements directly as
`mixed_after_products`, including the actual final call (no omitted return or
extra C statement). It derives the intervening T bound, preserves I/S1 and
all five allocations, returns exact X/Y/T/H3 words, reusable X/Y/T bounds
and a frame protecting Z and the flag.

`jet_secp_mixed_nonzero_tail.v:exec_mixed_nonzero_tail` composes the H test,
H-through-products prefix and X/Y suffix as the complete original nonzero-H
tail, deriving all intermediate storage/bounds and preserving Z/flag through
the X/Y operations. `jet_secp_mixed_finite_body.v:exec_mixed_finite_body`
attaches finite preparation and covers both H outcomes, from initial
point/affine fields and ten uninitialized owned temporaries. The H=0 path
reuses `exec_mixed_finite_zero_body` and preserves the three unused temporaries;
the nonzero path derives H/I and every later call from preparation.
`jet_secp_mixed_body.v:exec_mixed_body_owned` adds the actual incoming-infinity
branch. It executes the complete original `gej_add_ge_var` body for either
input flag, with r=a, NULL rzr and the affine input flag zero (the actual
public caller's shape). Outputs are the exact machine-coordinate functions,
flag, reusable bounds, ownership of the input point/affine allocations and all
ten temporaries, plus external framing. No H/I branch restriction,
intermediate execution or initialized-temporary premise is added.
`jet_secp_mixed_function.v:eval_mixed_function` now wraps that body in the
actual `Clight2.eval_funcall` for original `gej_add_ge_var` with r=a and NULL
rzr. It constructs the ten allocations and proves their freshness, all four
parameter bindings, the actual local environment and free-list order, the
void result for every return outcome and all ten frees. It preserves the
caller's point/affine ownership, coordinate outputs and flag/bounds, with
external framing outside those two caller allocations. No allocation,
intermediate-execution or freeing premise remains on this call theorem.
The affine input flag is zero, as established by the actual public reader;
the point's input infinity flag is unrestricted here. Next prove the literal
specification bridge and complete public reader/helper/writer lifecycle
before claiming public coverage. A C helper-call execution theorem is not
yet the public C-to-Simplicity equivalence theorem.

`jet_secp_add_literal_step.v:literal_gej_add_finite_step` exposes the fixed
literal program's finite dispatch and exact nonzero coordinate expressions,
by reduction of the original tree (not a replacement specification).
`jet_secp_mixed_dispatch_literal.v` relates the actual C H/I words to those
literal tests on all reader inputs: the literal H is the negative of C H,
so their zero tests agree; the I residues agree directly. The proved
`mixed_finite_zero_reader_outputs_literal` then connects both finite H=0
outcomes to the complete literal mixed-addition program: I=0 uses the
already-checked doubling output bridge, while nonzero I uses the original
writer's zero/infinity bridge. Its finite/H=0 hypotheses select internal
branches, not restrictions for a public registration. This also covers
off-curve inputs and the doubling path with zero Y; no on-curve or nonzero-Y
assumption is introduced. The nonzero-H bridge and branch composition are
described below. Coverage is unchanged until the complete public contract
is proved and accepted.

`jet_secp_mixed_nonzero_literal.v` now proves the nonzero-H X/Y/Z bridges,
reusing the selected square/multiply numeric results and the checked sum
bounds. It accounts for the literal H's opposite sign, the C negated H2,
H3/T products, the updated T used by Y, and the literal negative affine Z.
The named literal T/X/TX/Y/Z values are abbreviations for the exact expressions
exposed by `literal_gej_add_finite_step`, not alternative jet specifications.
`jet_secp_mixed_literal_bridge.v:mixed_nonzero_reader_outputs_literal`
instantiates them on actual reader words and proves equality to the full
literal mixed-addition program. `mixed_reader_outputs_literal` combines this
with both H=0 paths and incoming infinity, with no branch or input restriction.
`eval_mixed_literal` then composes the original helper's complete call theorem:
from the reader fields and flags, distinct owned point/affine storage, it
derives actual `Clight2.eval_funcall`, all output fields and reusable bounds,
the literal-program output, retained ownership and external framing. It has
no allocation, intermediate-execution or output-value premise and adds no
libc model. This is the complete helper-to-literal bridge, not yet the public
jet contract by itself. The public composition is now supplied by
`jet_secp_mixed_public_{reads,entry,body,prepare,rest,call}.v`:
both actual readers, all helper and writer calls, by-value frame copy, Boolean
return, three outer allocations and their exact frees are derived from
the standard general-frame preconditions. `jet_secp_point_output_literal.v`
reuses the original general writer for any proved literal output triple.
`jet_secp_mixed_local.v:gej_ge_add_literal_local_spec` closes the full original
public C-to-literal-Simplicity contract for arbitrary Word256 inputs,
including zero and off-curve coordinates, general valid cursors and unrelated
initial destination bits. No extra execution/output/library premise is added;
the theorem has the same six inherited execution assumptions. The endpoint
passed full ordinary scoped acceptance on the proof inputs of `63aa1380`:
431 kernel modules, 370 assumption modules, 385 contract modules, negative
tests and all five regenerated ASTs. The existing point source gate also checks the
GejGeAdd catalog mapping and exact public statement, rejecting eight new
targeted mutations. Reproduce acceptance with
`JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_ge_add`.

With the baseline Coq 8.17.1 and prepared jet dependencies, reproduce:

```sh
JET_TARGETS=C/jet_secp_mixed_head.vo bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_head
JET_TARGETS=C/jet_secp_mixed_infinite_literal.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_infinite_literal
JET_TARGETS=C/jet_secp_mixed_finite_start.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_finite_start
JET_TARGETS=C/jet_secp_mixed_copy_weak.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_copy_weak
JET_TARGETS=C/jet_secp_mixed_affine_product.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_affine_product
JET_TARGETS=C/jet_secp_mixed_s2_calls.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_s2_calls
JET_TARGETS=C/jet_secp_mixed_preparation.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_preparation
JET_TARGETS=C/jet_secp_mixed_difference.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_difference
JET_TARGETS=C/jet_secp_mixed_finite_prefix.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_finite_prefix
JET_TARGETS=C/jet_secp_mixed_zero_branch.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_zero_branch
JET_TARGETS=C/jet_secp_mixed_finite_return.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_finite_return
JET_TARGETS=C/jet_secp_mixed_nonzero_start.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_nonzero_start
JET_TARGETS=C/jet_secp_mixed_nonzero_products.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_nonzero_products
JET_TARGETS=C/jet_secp_mixed_y_tail.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_y_tail
JET_TARGETS=C/jet_secp_mixed_body.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_body
JET_TARGETS=C/jet_secp_mixed_function.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_function
JET_TARGETS=C/jet_secp_mixed_dispatch_literal.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_add_literal_step C.jet_secp_mixed_dispatch_literal
JET_TARGETS=C/jet_secp_mixed_literal_bridge.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_mixed_nonzero_literal C.jet_secp_mixed_literal_bridge
```

## Completed: fe_square_root

`C.jet_secp_root_local.fe_square_root_literal_local_spec` proves the original
public `simplicity_fe_square_root` against the fixed primitive-bearing
`fe_square_root` program in
`Haskell/Core/Simplicity/Programs/LibSecp256k1.hs`. This compares the actual
algorithms; it is not a theorem about mathematical square roots or primality.

The proof reuses the selected multiplication, square, reader, writer and
equality proofs. It executes the original addition chain, all eleven bounded
squaring loops and final comparison; derives all twelve helper allocations
and frees; and composes the public source-frame copy, reader, helper, temporary
assignments, bool conversion, tag and conditional payload/padding, return and
three outer frees. The standard local contract covers arbitrary Word256 inputs,
general valid cursors, word crossings and unrelated initial output contents.
Neither initialized-result storage, intermediate execution, mathematical
square-root facts nor a libc model is an extra final premise. Its assumption
snapshot retains the same six inherited execution assumptions.

The `jet_secp_root_*` modules are ordinary project sources. The entry/copy/call
adapters and the complete local endpoint compile in the normal build; focused
snapshots were reviewed. The existing `secp-field-integration/check-rescale.py`
checks the canonical catalog, exact tower/candidate/check ports and complete
public contract and rejects eighteen negative mutations. The proof inputs at
`fd51b860` passed ordinary scoped acceptance: 355 kernel modules, 294 assumption
modules, 309 contract modules, negative tests and all five AST regenerations,
with identical audit inputs before and after. Reproduce with:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_fe_square_root
```

Leave `simplicity_gej_ge_add_ex` unresolved: its equal-point ratio disagrees
with C on a legitimate noncanonical Word256 input, as documented in
[JET_SECP_RATIO_MISMATCHES.md](JET_SECP_RATIO_MISMATCHES.md). Do not fix that
target or restrict inputs while pursuing independent jets.

## Accepted mixed-equivalence endpoint

The selected endpoint for `simplicity_gej_ge_equiv` uses the fixed program
`take gej_negate &&& ih >>> gej_ge_add >>> gej_is_infinity`. The original C
helper `secp256k1_gej_eq_ge_var` allocates one fresh 128-byte temporary, negates
the input into it, performs in-place mixed addition and returns its infinity
flag. The public function reads a projective and an affine point and writes
one bit. It is now registered: the registry contains 502/533 jets, while
accepted local-contract coverage is now 502/533 after scoped acceptance.

Completed ordinary support, with normal builds, recursive kernel checking and
reviewed focused assumption/contract comparisons:

- `jet_secp_gej_ge_equiv_literal` ports the exact program and proves its
  parametricity/composition (closed). The existing correspondence gate rejects
  six mutations; this is not a public equivalence proof.
- `jet_secp_gej_negate_separate.eval_gej_negate_separate` derives the full
  original negation call into an uninitialized distinct destination: flag
  copy, three field copies, both Y arithmetic calls, entry and return.
  It returns all fields, flag, ownership and outside-result framing.
- `jet_secp_field_weak_loose` executes the actual weak-normalizer on limbs
  bounded by 2^60, retaining its changed output as `weak_loose_words`.
  It proves modular-value preservation and downstream `mul_small_input_bounds`
  (52-bit lower limbs and a 49-bit upper limb), without assuming canonical or
  positioned output. Its closed negated-reader lemmas identify the preceding
  negation's output and discharge the interval bounds.
- `jet_secp_mixed_copy_weak_loose` and `jet_secp_mixed_preparation_loose`
  derive the actual copy/normalize pairs and seven preparation statements.
  `jet_secp_mixed_finite_loose` composes both flag checks, the initial Z square,
  preparation and H/I differences. Raw point Y is preserved; S1 contains the
  actual normalized value, and I is derived from S1.
- `jet_secp_mixed_return_loose` covers H=0, including doubling and
  infinity-setting. `jet_secp_mixed_body_loose` covers every finite H/I
  branch and the incoming-infinity branch of the original body.
  Crucially, doubling consumes raw point Y while nonzero Y arithmetic uses
  normalized S1; neither representation is silently substituted for the other.
- `jet_secp_mixed_function_loose.eval_mixed_function_loose` derives the
  **complete original mixed-addition helper call** with NULL rzr, including all
  ten actual allocations/frees and return conversion. It needs only the two
  separated caller-owned points, represented inputs and their machine bounds;
  no initialized private field, intermediate execution or arithmetic result
  is a premise. It returns all result coordinates, the actual infinity flag,
  caller allocation ownership, output bounds and external framing.
- `jet_secp_gej_ge_equiv_function.eval_gej_ge_equiv_function` now derives the
  complete original `secp256k1_gej_eq_ge_var` call. It allocates its fresh
  128-byte temporary, derives negation's loose Y bounds, composes the three
  actual helper calls, converts the integer return and frees the temporary.
  It preserves both input allocations and external framing. The result is
  `gej_ge_equiv_result`, the actual C word/flag model, **not yet** the literal
  Simplicity program. Normal compilation, recursive kernel and focused
  snapshot checks passed with the same inherited assumptions.
- `jet_secp_gej_ge_equiv_reader` specializes that call to all five arbitrary
  Word256 reader outputs and proves the integer result is exactly zero or one.
  The `jet_secp_gej_ge_equiv_public_{reads,body,rest,call}` modules derive the
  **complete original public C call**, including entry, source-frame copy,
  both readers, helper, bit writer, return and all three outer frees. They
  require only one bit of output capacity and retain generic valid frame
  cursors and contents. `eval_gej_ge_equiv_public_c_bit` writes the C-derived
  `gej_ge_equiv_reader_bit`; this is not yet the literal specification.
- `jet_secp_gej_ge_equiv_dispatch` relates actual negated and weak-normalized
  reader limbs to the literal negative field value, then derives both H/I
  test correspondences. The generic residue-test adapters are reusable.
  `jet_secp_gej_ge_equiv_flag` proves agreement with the literal program for
  incoming infinity and both finite H=0 branches, including the actual
  doubled-Z flag. Its `equiv_finite_nonzero_h_reduction` proves that C returns
  false in the remaining branch while the literal program tests
  `(h * normalized_z * (feP - 1)) mod feP = 0`. These internal branch lemmas
  do not restrict the public input domain or complete public equivalence.
  Normal compilation, recursive kernel checking and reviewed focused
  assumption/contract comparisons passed. Pure bridges use at most the
  already inherited functional extensionality, not an assumed primality fact.
- `jet_secp_field_prime` checks a Pocklington certificate for the unchanged
  fixed modulus and derives reusable nonzero-product lemmas. All three
  theorem assumption records are **closed**. Normal build, recursive kernel
  and reviewed focused snapshot comparisons passed. The checksum-pinned
  CoqPrime v8.17 standard-integer checker subset builds under the existing
  Coq/OCaml baseline, both through the shell bootstrap and Nix; its accelerated
  bignums/native checker and certificate generator are not dependencies.
- `jet_secp_gej_ge_equiv_bridge.gej_ge_equiv_reader_matches_literal` closes
  the pure identity for every Word256 input, using the certified nonzero
  product fact in the finite nonzero-H case. The complete public theorem
  `jet_secp_gej_ge_equiv_local.gej_ge_equiv_literal_local_spec` composes it
  with the original public C execution and standard frame contract. Normal
  compilation, recursive kernel checking and reviewed focused assumption and
  contract comparisons passed. No curve, canonical-input, initialized-private
  storage, intermediate execution or primality premise is added.

Execution retains the same six inherited assumptions and no extra libc model.
The complete theorem uses the fixed literal Simplicity target. Its exact
whole-contract and canonical-port gate rejects thirteen targeted mutations,
and the registry selects this endpoint. Reproduce its checked closure:

```sh
JET_TARGETS='C/jet_secp_gej_ge_equiv_local.vo' bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_gej_ge_equiv_local
```

Scoped acceptance passed on `f1309893`, without update flags: 442 kernel-checked
modules, 381 assumption records, 396 contract records, source/negative checks
and all five original ASTs. Reproduce on that commit:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_ge_equiv
```

Keep production C, specifications, API contracts and generation settings fixed.
Do not replay the completed public wrapper or pure identity.

Do not apply the earlier `eval_mixed_literal` directly to negation's output:
its positioned-`fe_limbs_ok` Y premise is too restrictive. The loose-input
execution path above is the checked replacement for that internal boundary.
## Source-review question: Elements fee predicates

The canonical digest-equality test versus C's script-empty flag, exact source
locations, reproduction, verification limits and hypothetical impact are in
[JET_ELEMENTS_FEE_MISMATCHES.md](JET_ELEMENTS_FEE_MISMATCHES.md). No nonempty
preimage of the empty-script digest has been exhibited, and the needed
converse has not been proved. This is **not a demonstrated wrong result**.
Keep these unregistered targets unresolved and continue independent jets.

The current independent C-side task is the **processed** `sigOutput` classifier
`jets_elements.f_isFee` (`jets_elements.v:38964`), then its indexed public wrapper.
The archived `elements-env/.../jet_elements_env_isfee.v.source` is about a
different raw-output helper (script length and byte pointers); do not import it
as an execution proof of this function. Reuse the current Elements field and
indexed-wrapper infrastructure instead.

`C.jet_elements_fee_flag_exec.eval_processed_isFee` now proves the complete
original classifier call from initial field loads, through both short-circuit
branches, function entry, return conversion and local freeing. Closed layout
checks establish emptyScript=241, asset=0, amount=104, and both prefix fields
at +32 in the actual generated composite environment. The result holds for
either boolean flag and arbitrary integer prefixes, with empty trace and
unchanged memory. It adds no libc premise and retains the six inherited
assumptions. Normal compilation, independent recursive kernel checking and
reviewed focused assumption/contract checks pass on `c82ca174`. Reproduce
the focused checks using `JET_ONLY_MODULES` containing
`C.jet_elements_fee_flag_exec` with the existing audit scripts.

`C.jet_elements_fee_flag_caller.elements_output_fee_flag_contract` now composes
the original indexed public wrapper with that classifier, index reading,
presence/payload writes, absent-output padding and full function entry/return.
It reuses the existing indexed tag3 skeleton with arbitrary valid separated
frames and cursors. Its initial environment relation represents the actual
script-empty flag and asset/amount prefixes, not cached hash equality. The
result is explicitly `processed_fee_result`, **not** the canonical hash-based
program. Normal compilation and reviewed focused assumption/contract checks
pass, with the same six inherited assumptions and no libc premise. Independent
recursive kernel checking and the no-update focused audits also pass on
`d057851f`, in the clean task-owned verification worktree.

Neither module adds a registered jet. The full canonical empty-digest
converse above remains open.
The actual C-side value uses the raw-script-empty flag and explicit prefixes;
do not change that flag's representation to hash equality.

## Current scalar-multiplication milestone: literal signed scalar split

`C.jet_secp_split_literal` faithfully ports the full frozen
`scalar_split_lambda` Core program, including rounding, signed extension and
the final MSB/subtract/low-half selection. `jet_secp_split_half_numeric` and
`jet_secp_split_pack_numeric` establish those encodings; their exported
lemmas are closed. `jet_secp_split_numeric.literal_scalar_split_lambda_residues`
relates both literal halves to the already proved C scalar values for every
Word256 input, deriving the small bounds from the actual rounded coefficients.

`C.jet_secp_split_literal_function.eval_scalar_split_lambda_literal` composes
this with the complete original C helper call. It takes the canonical reader's
storage for an arbitrary input, uninitialized distinct output objects and the
original constant-state/ownership predicates; it returns the two literal
halves encoded as the scalars consumed by the signed window-5 proof. Input
storage, permissions, constants, readonly memory and framing are preserved.
No signed-output bound, intermediate execution or extra library model is a
caller premise. This remains an internal helper, adding no public coverage.

`jet_secp_wnaf_function5.eval_wnaf_literal5_slice` now proves the complete
original 129/5 call at every valid aligned output offset, retaining loads
outside its 516-byte slice. The signed array-step, bounded-loop, return and
post-memset proofs carry this stronger frame from the actual store effects;
their previous conclusions remain. The original offset-zero
`eval_wnaf_literal5` contract remains available as a proved specialization.
The only library premise is the already explicit `memset_model`.

`jet_secp_wnaf_pair5.eval_wnaf_literal5_pair` composes both original function
calls at offsets 0 and 516 of one 1040-byte Strauss point-state object. It
returns both literal digit arrays and both lengths, preserves both source
scalars and ownership, and retains every byte outside [0,1032), including
the two following length fields. No buffer initialization, digit result or
preservation fact is assumed. This closes the shared-object buffer boundary,
not the enclosing caller statements or a new public jet. Reproduce with
`JET_TARGETS=C/jet_secp_wnaf_pair5.vo bash Coq/build-jets.sh -j1`, scoped
audits of the six affected wNAF modules, and recursive `--coqchk` of
`C.jet_secp_wnaf_pair5`.

`jet_secp_strauss_wnaf_calls.exec_strauss_wnaf_prepare` now executes the
actual two wNAF blocks inside the one-point preprocessing iteration, including
all four state->ps pointer loads, original calls/casts, temporary updates and
the two length-field assignments. `strauss_wnaf_source` identifies those
blocks in the frozen Strauss body. The composite layout checks give array
offsets 0/516, count offsets 1032/1036 and object size 1040. Both literal arrays,
both returned/stored lengths, scalar inputs, ownership, state pointer,
permissions, readonly memory and outside-object loads are retained. Its final
contract assumes only the initial representations, local bindings, index
zero, ownership/separation and the existing `memset_model`; the internal
call-wrapper premise is discharged by `exec_strauss_wnaf_half`.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_wnaf_calls.vo bash
Coq/build-jets.sh -j1`, its scoped audits and recursive `--coqchk` on
`C.jet_secp_strauss_wnaf_calls`. These are caller blocks, not a complete jet.

`jet_secp_strauss_split_wnaf.exec_strauss_split_wnaf_prepare` now joins the
original split Scall to both original wNAF blocks for an arbitrary Word256
input stored by the canonical reader. Both literal signed halves, digit
arrays, stored lengths and their bounds are derived from those executions.
The proof retains the state pointer, all three scalar stores, ownership,
constant readiness, readonly memory and loads outside the combined footprint.
Separation from readonly constant objects follows from caller ownership; it
is not an extra address premise. `exec_strauss_split_wnaf_then_rest` attaches
this prefix to the exact remaining frozen caller statements. Only the
existing explicit `memset_model` remains as a library premise. This is an
internal prefix result; public coverage remains 520/533.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_split_wnaf.vo bash
Coq/build-jets.sh -j1`, its scoped statement/assumption audits and recursive
`--coqchk` on `C.jet_secp_strauss_split_wnaf`.

`jet_secp_strauss_bits_max.exec_strauss_bits_max` executes both original
length reads/comparisons and conditional pointer reloads, preceded by the two
actual assertion no-ops. It proves the final bit count is the maximum of the
two stored lengths, using the checked 0..129 bounds for signed C comparison;
memory is unchanged. `exec_strauss_scalar_prepare` composes this with the
split/wNAF prefix for every Word256 input and derives the maximum and its
bound. It retains both literal digit arrays, scalar stores, lengths, state
pointer, constant readiness, permissions, readonly memory, combined frame
and every caller temporary outside the actual write set. The existing
`memset_model` is its only library premise. The continuation lemma connects
this complete prefix to the exact remaining frozen point-table statements.
This is internal progress, adding no public jet (still 520/533).
Reproduce with `JET_TARGETS=C/jet_secp_strauss_bits_max.vo bash
Coq/build-jets.sh -j1`, its scoped statement/assumption audits and recursive
`--coqchk` on `C.jet_secp_strauss_bits_max`.

`jet_secp_strauss_table_call.exec_strauss_table_prepare` now derives the
original point copy, first-point odd-table caller and global-Z caller from
initial represented finite-point storage and ownership. It executes both
state pointer loads, the width/count/address expressions, both skipped
first-point conditional bodies and the no=0-to-1 counter update. It reuses
the checked actual helper calls and their literal `scalarTable5` bridge,
returning that exact table/result, bounds (including tight Y), the unchanged
source point, state pointers, caller permissions, readonly memory, outside
loads and untouched temporaries. The `eval_scalar_table5_calls` contract is
strengthened only by exposing its already proved first-call frame; all
previous premises and conclusions remain. This table component has no extra
library premise. The standalone `strauss_table_prepare` statement combines
two caller chunks; it is not a whole Strauss body or a public jet. The loop
composition below inserts the actual intervening controls.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_table_call.vo bash
Coq/build-jets.sh -j1`, scoped audits of this module and
`C.jet_secp_scalar_table_execution`, then recursive `--coqchk` on
`C.jet_secp_strauss_table_call`.

`jet_secp_strauss_first_loop.exec_strauss_preprocess_finite` now joins the
original scalar/wNAF/maximum prefix to the table component through the actual
preprocessing loop and global-Z statement. It covers the branch with a
nonzero canonical scalar and a finite input point, with no on-curve premise.
The scalar-zero call is derived from stored limbs and its existing verified
symbolic execution; the infinity accessor is reused. The proof executes the
initial np=0 assignment, both helper guards, complete iteration, np increment,
terminating comparison and final global-Z call. Both literal signed wNAF
vectors/counts and the literal scalar table hold together in the final memory;
the maximum bit count, source scalar/point, state pointers, all owned objects,
constants, readonly memory, frame and untouched temporaries are retained.
`strauss_preprocess_finite_source` identifies the two adjacent original body
statements. Intermediate call/loop executions are derived, not caller
premises; only the existing `memset_model` remains explicit. The table
component additionally exposes its already proved intermediate caller and
global-Z call so this proof can insert the original loop controls.
This is an internal finite/nonzero branch result, not public coverage. Zero
and infinity branches, actual Strauss entry/frees and the descending point
loop remain to compose; coverage stays 520/533.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_first_loop.vo bash
Coq/build-jets.sh -j1`, scoped audits of this module and
`C.jet_secp_strauss_table_call`, then recursive `--coqchk` on
`C.jet_secp_strauss_first_loop`.

`jet_secp_strauss_beta_prepare.exec_strauss_point_prepare` now composes the
finite/nonzero preprocessing and global-Z statements with all eight actual
beta-loop iterations. The three consecutive original body statements are
identified by `strauss_point_prepare_source`. The result retains both signed
literal wNAF vectors/counts, the original maximum count, literal scalar table
and tight Y bounds, and adds the stored beta products with their exact
`literal_fe_multiply_beta` values and bounds. It also retains source scalar
and point storage, state pointers, all owned objects, split constants, beta
initialization, readonly memory, combined framing and untouched temporaries.
Separation from beta is derived from each caller object's first owned byte
and the original constant's readonly permissions. No extra address premise,
helper execution or desired product is assumed. The only library premise
is the existing `memset_model`; `beta_initialized` is the same initialized
program-state predicate already established from `Genv.init_mem` and is
transported through the preprocessing proof's readonly preservation.
This remains the internal finite/nonzero branch, not a public jet; coverage
stays 520/533. Reproduce with
`JET_TARGETS=C/jet_secp_strauss_beta_prepare.vo bash Coq/build-jets.sh -j1`,
its scoped statement/assumption audits and recursive `--coqchk` on
`C.jet_secp_strauss_beta_prepare`.

`jet_secp_strauss_skip.exec_strauss_no_points` now covers the other
preprocessing cases: the represented scalar is zero, or the input point's
infinity flag is one. The zero-scalar path reuses the original checked
preprocessing proof; the nonzero/infinity path executes both actual helper
calls and the original `continue`. The result composes initialization,
increment/termination, the zero-length global-Z call (including its private
allocations/frees) and the skipped beta loop. All old memory, permissions and
readonly state are preserved; the final no/np counters are zero and other
temporaries outside the actual write set are retained. No table initialization,
helper execution, desired output or external-library model is assumed. This
complements the finite/nonzero result without asserting values for unused
point tables or wNAF arrays. It is still an internal original-body phase,
not a registered public jet; coverage stays 520/533.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_skip.vo bash
Coq/build-jets.sh -j1`, its scoped statement/assumption audits and recursive
`--coqchk` on `C.jet_secp_strauss_skip`.

`jet_secp_generator_entry.strauss_entry_owned` now factors the actual nine
local allocations for arbitrary scalar arguments. It derives the original
function entry, mutual separation, freshness from old memory, all nine local
ownership ranges, and preservation of old loads, permissions and readonly
state without any input-value or initialized-global premise.
`strauss_entry_and_initialize` composes that entry with the original initial
counter assignments and Z=1 helper call, retaining all local ownership and
preserving all old memory. The existing `generator_entry_and_prepare` reuses
the shared allocation proof with its original statement unchanged; its
zero-scalar restriction is not imposed on the new general entry result.
These are internal entry/prefix results, not another whole-public jet.
Reproduce with `JET_TARGETS=C/jet_secp_generate_local.vo bash
Coq/build-jets.sh -j1`, scoped audits and recursive `--coqchk` on
`C.jet_secp_generator_entry`.

`jet_secp_strauss_program` supplies the literal descending-step target from
LibSecp256k1.hs:634--660: doubling, optional ordinary and lambda window-5
additions, then both optional generator additions through the current Z.
Its `step2` through `step128` and `step129` retain the original four-digit
routing and unchanged Z/table context. The step-value, block and 129-digit
list-fold theorems expose the precise operation order for the C loop proof;
all ports are algebra-parametric. It reuses the checked window-5/window-15
flattenings and the existing list-combination lemma. This is literal
specification support, not a C loop or public-jet theorem. The enclosing
body/guard and whole-jet composition are still pending. Reproduce with
`JET_TARGETS=C/jet_secp_strauss_program.vo bash Coq/build-jets.sh -j1`, its
scoped statement/assumption audits and recursive `--coqchk`.

`jet_secp_strauss_digit_guard.exec_strauss_digit_dispatch` now executes either
complete original window-5 dispatch in the descending loop. Its guard derives
the actual PS pointer/count loads, the second PS reload and positioned digit
read, signed n assignment and bool conversion. Indices past the stored count
take the short-circuit branch without requiring a digit load. An absent digit
skips the calls; a nonzero nibble derives the original ordinary/lambda lookup
and mixed-addition calls through `jet_secp_strauss_digit_add`, retaining
precise literal coordinates, bounds, the flag/Z invariant, ownership,
readonly preservation, old permissions and caller framing. Both statement
adapters are definitionally the corresponding original AST subtrees.
`jet_secp_mixed_xy_framed` composes the existing loose-coordinate execution,
literal-output and flag proofs; no helper execution or desired output is an
assumption of the dispatch result. Its only representation inputs are the
table, beta array, counts/digits, accumulator and ownership already supplied
by the caller/preprocessing contracts. `strauss_digit_actions_literal` ties
the ordinary/lambda actions after doubling to the literal four-window step
when the two generator digits are absent, as needed by `off_curve_scale`.
These are internal original-body results; coverage remains 520/533.
Reproduce with `JET_TARGETS=C/jet_secp_strauss_digit_guard.vo bash
Coq/build-jets.sh -j1`, scoped statement/assumption audits of the three new
modules and recursive `--coqchk` on `C.jet_secp_strauss_digit_guard`.

`jet_secp_strauss_point_loop.exec_strauss_single_point_loop` composes both
dispatches into the complete original one-point inner loop, including np
initialization, increment and termination. The real state/PS loads, high
count/digit read and table/beta representations are transported through the
first dispatch's frame before executing the second. Both dispatch executions
are derived, and the result retains their exact nested literal actions,
canonical flag/Z invariant, coordinate bounds, owned ranges, permissions,
readonly state, memory framing and unaffected temporaries. It assumes neither
an intermediate execution nor a desired result. The normal build target is
`C/jet_secp_strauss_point_loop.vo`; use its scoped statement/assumption audits
and recursive `--coqchk`. This remains an internal loop, not a public jet.

`jet_secp_strauss_scale_iteration.exec_strauss_scale_iteration` composes the
original doubling call, one-point loop and both skipped generator dispatches.
For a state with no=1 and zero generator counts it returns exactly one literal
four-window Strauss step, including degenerate off-curve intermediates.
It assumes no Z=1 property or inactive generator-array initialization.
`jet_secp_strauss_scale_loop.exec_strauss_scale_loop` inducts over all counts
0..129 and executes the original descending loop through i=-1. It derives
every iteration and transports the state/PS loads, counts, arrays and
table/beta representations through their proved frames. It retains exact
literal-step results, bounds, flag/Z consistency, ownership, permissions,
readonly state, framing and unaffected temporaries. Its pure fold and
leading-zero lemmas connect the variable C loop length to the fixed literal
129-step construction without changing operation order. These are internal
finite-point/zero-generator-count results, not whole public jets.

`jet_secp_strauss_generator_zero.exec_strauss_zero_wnaf_setup` executes both
original window-15 calls on zero scalar halves and both maximum-count tests.
The zero lengths are derived from the literal digit vectors and C's last-
nonzero-digit invariant; they are not assumed results. The existing point
bit count is retained, including when it is nonzero. Scalar inputs need only
the existing readable representation; the digit buffers are owned. This
setup retains the approved `memset_model` premise and does not include the
preceding split_128 call. Reproduce the three modules with normal targets
`C/jet_secp_strauss_scale_loop.vo C/jet_secp_strauss_generator_zero.vo`,
their scoped statement/assumption audits and recursive `--coqchk` on both
roots. Coverage remains 520/533.

`jet_secp_strauss_zero_generator` describes the actual `_ng` static const
scalar of `off_curve_scale`. Its zero words and readonly permission bounds
are established from `Genv.init_mem jets_secp.prog`, using symbol lookup rather
than a numeric block identifier. `exec_strauss_zero_generator_branch` composes
the real nonnull-pointer test, borrowed-input split_128, both window-15 calls
and both maximum-count tests. It derives zero generator counts while retaining
any current point bit count in 0..129, the zero halves, all four private owners,
the readonly global, all old permissions and external framing. Only the existing
`memset_model` is assumed for the external clear; no ownership of the global
or assumed intermediate call is required.

`jet_secp_strauss_digit_index` recovers typed window-5 digits, exact signed
integer loads and absence above the returned count from the preprocessing
array/list relation. The pair-vector theorem supplies the literal 129-digit
routing needed by the descending-loop bridge, including negative signed
halves. `jet_secp_strauss_final_literal.exec_strauss_final_literal` executes
the original final Z correction for any represented table denominator. In
the infinity branch, skipping the multiply agrees with literal multiplication
because the normalized input Z is zero. It requires neither Z=1 nor a nonzero
denominator. The original flag is retained; no new flag/output-Z invariant
is claimed after this correction.

`jet_secp_strauss_empty_stage.exec_strauss_empty_point_stage` composes the
actual infinity initializer, i=-1 assignment, zero-length descending-loop exit
and skipped final correction. It derives all zero coordinates, the flag,
ownership, framing and unchanged permissions without reading or representing
inactive tables, digit buffers or the denominator. These four modules close
caller obligations, not new public jets. Normal build targets are their four
`.vo` files; use their scoped statement/assumption comparisons and recursive
`--coqchk` on all four modules. Coverage remains 520/533.

`jet_secp_strauss_complete_program` ports the complete literal body, guard
and `off_curve_scale` wrapper from LibSecp256k1.hs:628--672. Small abstract
routing lemmas keep the scalar split, digit programs, table builder and
129-step fold opaque during value proofs; they do not replace those operations.
The body retains the final multiplication in its original argument order.
Its guard selects `generate` for a zero scalar or an infinite point.

`jet_secp_strauss_scale_literal` derives the fixed literal 129-step result
from the two signed C preprocessing arrays and their already-proved literal
value relation. The omitted leading digits are derived absent from the
returned-count invariant. Both generator streams are derived from the literal
split of the zero scalar. `strauss_scale_body_from_arrays` then identifies
the loop and final correction with the complete literal body. The skipped
preprocessing branch uses the separately proved `strauss_generate_zero`.
These are representation/specification bridges; they assume no C execution
or desired output equality.

`jet_secp_strauss_scale_point_stage.exec_strauss_scale_point_stage` composes
the original infinity initializer, countdown assignment, entire descending
loop and arbitrary-denominator final correction. Its output is the exact
short-loop result with the original final Z multiplication. It retains
coordinate bounds, all five owned ranges, old permissions, readonly memory
and external framing. No on-curve, Z=1 or nonzero-denominator premise is
added. The ordinary-local-environment condition is discharged separately for
the actual nine-local `generator_local_env` by `strauss_local_env_plain`.
Normal targets are these three modules' `.vo` files; use their scoped audits
and recursive `--coqchk` on the three roots. The updated header of
`jet_secp_strauss_final_literal` only corrects its earlier Z=1 description;
include that module in the scoped comparison. Coverage remains 520/533.

`jet_secp_strauss_scale_main.exec_strauss_scale_main` composes the actual
zero-generator scalar branch with the admitted-point stage. It transports the
preprocessing arrays, counts, state pointers, table, beta products and denominator
through the branch's proved frame. The resulting coordinates equal the complete
literal body, not just the short recurrence. All local owners, old permissions,
the readonly zero scalar and external framing are retained. Its empty main-stage
theorem requires neither a point table nor point digits.

`eval_strauss_scale_skipped` executes the entire original Strauss function when
the non-generator scalar is zero or the input point has its infinity flag set.
It derives the real entry, initialization, skipped preprocessing, zero-generator
branch, empty point stage and all nine local frees. The result has zero coordinates,
infinity flag one, the original output ownership, readonly-global state and
framing outside the result block. The only extra library premise is the existing
`memset_model`; scalar input storage is readable, with no ownership requirement.
This whole helper-call theorem covers the skipped branch, not every input of the
public jet. Reproduce with `JET_TARGETS=C/jet_secp_strauss_scale_main.vo bash
Coq/build-jets.sh -j1`, its scoped audits and recursive `--coqchk`.

`jet_secp_strauss_scale_function.eval_strauss_scale_finite` now executes the
entire finite/nonzero Strauss call: actual entry and initialization, scalar split,
both signed windows, table/global-Z/beta preprocessing, main stages and all nine
frees. Separation comes from the actual fresh allocations. Readonly constants
omitted by the conservative preprocessing frame are restored using the proved
readonly preservation. The result is the complete literal body.

Its `eval_strauss_scale` combines this with the skipped call and derives which
branch applies from the canonical scalar zero test and the actual input point
flag. The coordinates equal `literal_off_curve_scale` for either branch. Its
seven caller-owned objects are result/scalar/point/state/digits/table/auxiliary
storage; this internal contract does not pretend the latter four are unchanged.

`jet_secp_ecmult_scale.eval_ecmult_scale` supplies those four auxiliary objects
through the original outer function's actual allocations and state stores,
calls Strauss, and releases all four. It preserves the three public-wrapper
local owners and frames all other old blocks. The original external memset
contract remains the only additional library premise in these call theorems.

`jet_secp_scale_public_reads.eval_scale_public_reads` derives both original
scalar/point reader calls from general valid input/output frames and cursors.
It preserves the scalar through the point reader and supplies all three point
fields, the actual infinity flag, local owners and the output-frame invariant.
Neither desired reader execution is assumed.

Reproduce by building `C/jet_secp_strauss_scale_function.vo`,
`C/jet_secp_ecmult_scale.vo` and `C/jet_secp_scale_public_reads.vo` with
`JET_TARGETS`, their scoped assumption/contract audits, and recursive
`--coqchk` on the three roots. Those three roots passed the ordinary build,
scoped assumption/contract comparisons and recursive kernel check, with the
expected inherited axiom set and no unsafe proof features.

The next public candidate is now in ordinary modules:

- `jet_secp_scale_startup` establishes the zero auxiliary scalar, split
  constants and beta state from the original `Genv.init_mem`, proves a real
  initialized memory exists, and transports readiness through the actual calls.
- `jet_secp_scale_public_support` supplies all four wrapper allocations,
  the private source-frame copy, the exact scalar/point/ecmult/writer call
  spine, readonly point-reader preservation, and all four local frees.
- `jet_secp_scale_lifecycle.eval_off_curve_scale_initialized` derives that
  entire original public C execution from arbitrary valid frames/cursors and
  four unrestricted input words. Every helper execution and representation
  premise is discharged. It proves the literal output, external framing,
  output-frame invariant and final startup state.
- `jet_secp_scale_local.off_curve_scale_initialized_local_spec` packages the
  exact standard initialized local contract, conditional only on the existing
  `memset_model`. No curve-membership or extra input-domain restriction is added.

All four modules compile with the pinned toolchain. Reproduce with
`JET_TARGETS=C/jet_secp_scale_local.vo bash Coq/build-jets.sh -j1` and their
scoped assumption/contract audits. The public candidate is **not registered or
accepted yet**: its independent kernel/scoped acceptance check and complete
canonical-source binding remain. A read-only Astra Medium review found no
discrepancy in the five outer ports (complete program, Strauss step/traversal,
scalar table, lambda split, wNAF5), but did not certify the full dependency
closure. Extend the existing `secp-field-integration/check-rescale.py` gate
with exact Haskell/Coq port comparisons and targeted mutations, covering or
reusing checks for the remaining lookup, scalar/wNAF and generator dependencies
actually used by this zero-generator specialization. A structural port review
does not itself establish C execution or acceptance. Keep coverage at 520/533
until the public proof passes acceptance; the all-jets goal remains active.
For the descending loop's doubles, reuse
`jet_secp_double_loose_literal.eval_double_var_loose_literal`: it executes
the original `gej_double_var`, which recomputes the infinity flag from Z,
and retains that flag/Z relation for degenerate off-curve intermediates.
Derive all helper preconditions there and retain the original zero/infinity
branches. The wrapper passes a nonnull generator-scalar pointer containing
zero, so its generator branch still executes. The existing generator-addition literal contract
assumes Z=1; do not impose that restriction on the finite point table's Z.
`off_curve_scale` skips both generator additions because their digits are
absent; the broader linear-combination jets need an arbitrary-Z bridge.
Preserve literal operation order for off-curve inputs instead of substituting
an abstract elliptic-curve scalar identity.

Reproduce the split bridge build with
`JET_TARGETS=C/jet_secp_split_literal_function.vo bash Coq/build-jets.sh -j1`;
use the existing scoped audits for `C.jet_secp_split_numeric` and
`C.jet_secp_split_literal_function`, then recursive `--coqchk` on the latter.
