# Remaining jet proof work

The current local-contract registry contains 467 of the 533 header declarations.
Selected registrations, verification status and their conditions are listed in
[JET_ACCEPTANCE.md](JET_ACCEPTANCE.md); 66 declarations remain unregistered.

The remaining work includes:

- shared frame-domain and evaluator admissibility;
- exhaustive inherited correspondence to canonical programs;
- general caller startup and persistent SHA/global-state readiness;
- libc implementation proofs where a contract assumes `memcpy_model`;
- raw transaction/taproot projections for cached Bitcoin environment fields.

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

## Candidates: Elements input and taproot hash getters

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
not registered or accepted yet.

## Source-review question: Elements fee predicates

Before attempting `output_is_fee` or `total_fee`, investigate this boundary:

- `Haskell/Simplicity/Elements/Programs/Transaction.hs` defines `outputIsFee`
  using equality of `OutputScriptHash` with `bsHash mempty`, together with the
  explicit asset/amount tests.
- `C/elements/elementsJets.c` uses `output->emptyScript` in `isFee`.
  `copyOutput` in `C/elements/env.c` sets this flag from script length zero.

For actual builder-produced environments, the missing converse is that a script
with the empty-script digest is empty, within the supported script domain.
No such property has been proved here, and no nonempty script with that digest
has been exhibited. This is a source-level proof obligation, **not a formal
counterexample or a demonstrated wrong result**. Do not assume digest-preimage
uniqueness or redefine the flag's representation to hide the obligation. Keep
these unregistered targets unresolved while investigating or reporting closed
evidence, and continue independent jets.
