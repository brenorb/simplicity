# Original C field-negation helper

Current milestone: see [ACCEPTANCE-CANDIDATE.md](../README.md) for
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

The existing literal `multiply_word_spec` and `multiply_word_spec_numeric`
already support the 256-to-512-bit multiplication bridge without a carrier-width
restriction. `modulo_word_spec` lives in `jet_division_core_spec`, not a module
named `jet_modulo_spec`. Its general numeric bridge is already available as
`div_mod_word_numeric` / `division_word_spec_numeric` in
`jet_division_result_spec`; specialize at depth 9 for 512 bits rather than
attempting new recursive division proofs. Preserve the canonical combinator
composition and inspect the literal-source correspondence of these dependencies.

Next discharge the limb bounds from normalized reader
output, connect the existing field normalizer/writer and the literal
canonical bridge. Then reuse the public entry/allocation/copy/free machinery
for the whole `simplicity_fe_negate` jet, with full output/cursor/memory facts.

All work is separate from the frozen range-acceptance inputs. The unrelated
untracked `Coq/C/jet_secp_fe_negate_math.v` is read but left unchanged.

## Current implementation link and next obligation

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
