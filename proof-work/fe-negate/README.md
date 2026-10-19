# Original C field-negation helper

Current milestone: see [ACCEPTANCE-CANDIDATE.md](ACCEPTANCE-CANDIDATE.md) for
the freshly built isolated 23-module literal-specification candidate, live
snapshot audit and remaining acceptance obligations. Historical checkpoints
below do not supersede that status; accepted coverage remains unchanged.

The complete helper executes the actual `f_secp256k1_fe_negate` in place with
magnitude argument one. Its initial premise is an owned, represented field
region, not execution or an output fact. It derives the original Clight call,
final symbolic representation, unchanged region shape and outside-memory
framing. Compilation and independent whole-chain kernel checking pass; public
jet equivalence and acceptance remain open. Exact hashes/receipts are in the
manifest. The six per-result assumptions are inherited, not new declarations.

Do not substitute an integer `p - x` operation for the canonical specification.
The pinned catalog binds `FeNegate` to `fe_negate`; the literal program expands
to `fe_multiplyInt (-1)`, i.e. multiplication by the scribed `(-1 mod fieldOrder)`
followed by `fe_normalize512`. That reduction is the actual `Arith.modulo word512`
composition. Its shared bridge can also support field add/square/multiply; the
simple integer identity is an intermediate lemma, not the specification.

`jet_secp_field_negate_values.v.source` now derives all five concrete machine
loads from the final representation and combines them with the actual helper
call, representation, shape and outside-memory framing. Its seven lemmas compile
as a whole module (session 38829). The indexed machine result is
`Int64.sub (Int64.repr (4 * negate_mask n)) (rho (S n))`; under the reader's
52/48-bit limb bounds its unsigned value is exactly the integer subtraction.
The numeric bridge is closed under the global context. Independent whole-chain
kernel checking passes with exit 0 (session 21911), retaining 15 existing
allowlisted library axioms and no unsafe flags; no public acceptance is claimed.

The existing literal `multiply_word_spec` and `multiply_word_spec_numeric`
already support the 256-to-512-bit multiplication bridge without a carrier-width
restriction. `modulo_word_spec` lives in `jet_division_core_spec`, not a module
named `jet_modulo_spec`. Its general numeric bridge is already available as
`div_mod_word_numeric` / `division_word_spec_numeric` in
`jet_division_result_spec`; specialize at depth 9 for 512 bits rather than
attempting new recursive division proofs. Preserve the canonical combinator
composition and inspect the literal-source correspondence of these dependencies.

The separate `jet_secp_field_negate_normalize` repairs the earlier experiment's
unfold/rewrite order, missing list notation and incorrect rewrite of the input
limb expression. It compiles and passes independent whole-chain kernel checking
(sessions 77819/49844). Its machine-limb normalization bridge is closed under the
global context; this is support for the real writer, not a substitute jet.

`jet_secp_canonical_negate` now ports the actual scribed multiplication factor,
256-to-512-bit multiplication, and literal modulo/projection composition.
Its numeric proofs work over the full Word256/Word512 domains and are closed
under the global context. Compilation passes (83662); independent kernel
checking passes with exit 0 (37096, `canonical-kernel.log`). Keeping recursive modulo
opaque avoids expensive proof-closing conversion; the semantic proof uses the
existing checked general division theorem. The three algebra-independent
parametric proofs also compile in a separate module (56169), with closed final
assumptions; their independent kernel check passes with exit 0 (51928,
`parametric-kernel.log`, same 15 inherited library axioms and no unsafe flags).
Literal correspondence and a negative-tested gate
still need review before any acceptance.

Next discharge the limb bounds from normalized reader
output, connect the existing field normalizer/writer and the literal
canonical bridge. Then reuse the public entry/allocation/copy/free machinery
for the whole `simplicity_fe_negate` jet, with full output/cursor/memory facts.

All work is separate from the frozen range-acceptance inputs. The unrelated
untracked `Coq/C/jet_secp_fe_negate_math.v` is read but left unchanged.

## Current implementation link and next obligation

`jet_secp_field_negate_storage` compiles (51981): the actual helper call derives
`fe_at` with all five output limbs and keeps Freeable storage for cleanup.
`jet_secp_field_negate_calls` compiles (28365): reader-compatible initial limb
bounds and value imply actual negation and actual normalization calls, producing
the literal canonical negation's field representation. Both per-call memory
frames and intermediate Freeable permissions are retained. Their independent
whole-chain kernel check passes with exit 0 as 56432 (`calls-kernel.log`),
with 15 inherited library axioms and no unsafe flags. Neither
theorem is a public wrapper equivalence or an assumption of its output.

The real `f_write_fe` body (generated AST line 201310) calls normalize_var,
then get_b32, then write8s, with a local 32-byte array. Negated intermediate
limbs can exceed the existing writer numeric theorem's 52-bit initial bound.
Do not assume that theorem applies or insert an extra normalizer call before
the real writer. Use the checked normalization as its first actual statement,
then connect get_b32/write8s and storage cleanup; alternatively generalize the
writer's symbolic/value contract with all obligations discharged.

The reader normalizes arbitrary Word256 input. Discharge the calls theorem's
`< feP` value premise with that reader result, and prove canonical negation
unchanged by canonical input normalization. The original full Word256 domain
must remain in the final public contract. Finish canonical source/negative gate,
snapshots and independent acceptance before registering any coverage.

## General writer now available

Three new wide-writer modules compile (7676, 71491, 18687). The original
condition and byte expressions satisfy interval checking with initial limb
bounds `0..2^60`, so no replacement helper or extra normalizer call is needed.
The shared numeric/machine-byte theorem derives big-endian bytes of the field
value modulo `feP`; its final assumption set is closed. It supports limbs
larger than 52 bits, including magnitude-one C negation's intermediate result.

`eval_local_wide_write_fe` derives the whole original `f_write_fe` call from
initial represented Freeable storage, interval bounds, external separation and
the existing input/output frame invariant. It retains encoded output, final
`finv` (output/prefix/cursor/memory observations), final storage representation
and outside-memory framing. The six inherited execution assumptions are
unchanged. Independent joint kernel checking passes with exit 0 as 42447,
`wide-writer-kernel.log` (15 existing library axioms, no unsafe flags);
no integration or coverage is claimed.

Prefer this shared theorem to separately reconstructing the writer's internal
normalization/get_b32/write8s calls. The two-call theorem remains checked
diagnostic support, not a changed public call sequence. Next build the writer
initial representation from `negate_values`/`fe_at`, relate `wide_fe_output` to
literal canonical negation, transport the reader's frame invariant across
negation, and retain Freeable storage via the final representation. Then use
the established public entry/by-value source copy/return/free machinery.

## Complete public candidate (latest)

The five new reader/body/rest/lifecycle/local modules compile freshly. The
final `fe_negate_local_spec` instantiates the unchanged shared public contract:
actual original public C call, canonical encoded output, prefix, cursor and
outside-memory loads, with allocation, real by-value source copy and local
freeing all derived. Arbitrary Word256 inputs are retained; the internal
normalized-value bound is discharged from the actual reader, not added as a
public premise. Printed final assumptions contain the six inherited execution
assumptions, without a `memcpy_model` premise.

The previous combined-call kernel check (62934) passes with exit 0. Independent
whole-chain kernel checking at the default stack limit terminated with exit
129 and `Fatal Error: Stack overflow` (36723). The corrected run with the
established 65520 KiB stack **passes with exit 0** (10047), log
`/tmp/jet-fe-negate-next.GYJw0C/public-negate-stack64-kernel.log`: 15 existing
library axioms, no unsafe/type-in-type/assumed-positivity flags.
Canonical source correspondence/negative gate,
snapshot review and independent full acceptance remain required before
integration or registration; accepted coverage remains 349/533.

Reproduce compilation from `/tmp/jet-range-consumer.RbIhbg/Coq` with the pinned
Coq 8.17.1 PATH and `bash build-jets.sh --coqc -R
/tmp/jet-fe-negate-next.GYJw0C C -q SOURCE.v`, in manifest dependency order.
The original untracked math experiment is preserved unchanged.

The new `check-negate-wiring.py.source` actively compares the catalog binding,
literal `fe_multiplyInt (-1)`/multiply/normalize512 wiring, constant conversion,
specialized widths, Coq port bodies, multiplication/modulo wrappers and exact
complete public statement. `test-negate-wiring.py.source` rejects 19 meaningful
mutations. Run it with `--repo REPO --candidates MATERIALIZED_COQ_DIRECTORY`;
tests mutate only in-memory source text, not audit inputs.

This is a scoped correspondence gate, not a transitive fidelity certificate.
`CANONICAL-REVIEW.md` records the inspected literal multiplication/division
core mapping and the remaining transitive obligations. The existing normalize
correspondence gate also passes on current accepted sources.
Before registration, review recursive `fullMultiplier`, `div_mod`/pre/post
shift/div2n1n/div3n2n ports and representation/notation/constant conversion
against their canonical sources, reusing existing reviewed evidence where it
actually covers these dependencies. The existing normalization gate checks the
field-order constant and shared full public contract; run that too. Snapshot
review, independent acceptance and integration remain separate obligations.

The inspected recursive declarations and implementation regions are now
frozen in `recursive-ports-review.json`. The recursive gate passes on both
accepted and reconciled-range sources; its in-memory tests reject 43 mutations.
Run `test-recursive-ports.py.source --repo REPO --candidates
proof-work/fe-negate`. These scoped checks do not close the remaining
transitive bit/arithmetic/type/encoding review in `CANONICAL-REVIEW.md`.

## Combined calls and reader-domain bridge

Latest foundation receipt: `check-foundations.py.source` passes and the
companion suite rejects 32 mutations of conversion/type/scribe/notation or
inactive source. It supplements the closed, kernel-checked state-conversion
bridge. Prepare the acceptance candidate with the literal final contract,
parametricity module, all reviewed program definitions and four source gates;
review actual type/definition/assumption additions before final acceptance.
Do not modify checkout inputs during live run 24458. No new registration is
claimed by these separate checks.

Latest dependency follow-up: the recursive source gate is expanded to 48 typed
Coq declarations and 16 Haskell regions; all 86 mutations reject. Literal
negation parametricity passes kernel checking with exit 0 (90456).
`jet_haskell_word_conversion.v.source` now formally bridges the low-first
Haskell-style state traversal to `fromZ` at every width/integer, including its
final quotient. It compiles closed; kernel checking passes with exit 0 (1799). Conversion,
type/scribe/notation source gates and acceptance remain pending.

Latest literal-add follow-up: `jet_literal_division_add.v.source` lifts the
canonical addition adapter through all affected correction/recursive division
programs and modulo. `jet_secp_negate_literal_contract.v.source` proves the
complete public contract against negation using that literal-add modulo.
Both compile, with the six inherited public execution assumptions unchanged.
Independent final whole-chain kernel check passes with exit 0 (32921); log
`/tmp/jet-fe-negate-next.GYJw0C/literal-contract-kernel.log` (15 existing library
axioms, no unsafe flags). The literal-port gate passes and rejects 15 mutations.
The separate algebra-independent parametricity module compiles with its final
result closed; whole-chain checking runs as 90456. Remaining transitive
dependencies, snapshot review and acceptance are open; coverage is unchanged.

Three further modules compile (93928, 46070, 41832): canonical negation is
unchanged by canonical reader normalization for arbitrary Word256 inputs;
negation storage constructs the wide writer's initial representation and its
output equals literal canonical negation; final writer storage retains Freeable
permissions. `eval_negate_write_calls` derives both actual C calls, canonical
encoded output, finv, final Freeable field storage and composed memory framing.
It transports the input/output invariant across the real negation stores, not
by assuming the later output or an unchanged-memory fact. Independent combined
kernel checking is running as 62934 (`negate-write-kernel.log`).

Next use `eval_local_read_fe_canonical` / its capacity variant. Choose the
normalized input as the internal `x`; derive its exact limbs/value/bounds from
the reader's `fe_at`, then construct the initial `write_fe_rho` representation.
Use the existing read-final-to-write-initial invariant bridge, proving all
copied source metadata/storage preservation through the combined calls.
Rewrite the final result with `canonical_fe_negate_normalized_input` so the
public contract retains the original arbitrary input. Adapt the established
normalize/odd/zero public entry/source-copy/rest/free proof structure to the
actual negate AST. The `< feP` premise belongs only to the normalized internal
value; it must never become a restriction on the public jet's input.
