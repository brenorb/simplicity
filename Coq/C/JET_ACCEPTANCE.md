# Integration and pending-jet reconciliation

The history cleanup preserves the implementation and canonical specification.
Mismatches belong in `JET_*_MISMATCHES.md` for the Simplicity developers.
The local-contract registry contains 480/533 jets (351 without an extra libc
premise; 129 conditional on `memcpy_model`). The earlier 430-entry baseline passed
full acceptance; the additional `gej_rescale` and `sha_256_block` endpoints
and ten context-add endpoints passed scoped acceptance, followed by buffer-add
and finalization. TapData then passed the fourteen-jet scoped acceptance below.
The four Bitcoin SHA registrations then passed the scoped acceptance below.
Tappath hash then passed the expanded consumer acceptance below.
The four array-hash registrations then passed ordinary scoped acceptance below.
The five array/tappath rows now select accepted raw-interpretation variants,
without a change to the coverage count; their scoped acceptance is recorded below.
The two tapleaf/tap-environment registrations then passed scoped acceptance below.
The three input outpoint/annex/combined-hash registrations then passed ordinary
scoped acceptance below.
The single-input Bitcoin hash and seven Elements array-hash registrations then
passed ordinary scoped acceptance below.
The five further Elements input/taproot hash registrations then passed ordinary
scoped acceptance below.
The four Elements issuance-proof/nonce/amount-hash registrations then passed
ordinary scoped acceptance below.
Three Elements composite/blinding-hash registrations and issuance status then
passed ordinary scoped acceptance below.

Reproduce acceptance from the repository root:

```sh
bash Coq/check-jets.sh --accept
```

The commit and this command are the evidence. Logs stay outside the repository.

## Candidate reconciliation

Claude’s approximate pending list contained three partial-name search hits.
The 33 actual jets plus the overlooked entropy and beta endpoints are accounted
for below. Twenty-five were already in the separately verified 420-jet integration;
ten are newly accepted registrations.

| Jet | Registration |
| --- | --- |
| `asset_amount_hash` | New accepted local contract |
| `broken_do_not_use_check_lock_distance` | Existing verified integration |
| `broken_do_not_use_check_lock_duration` | Existing verified integration |
| `calculate_asset` | New accepted local contract |
| `calculate_confidential_token` | New accepted local contract |
| `calculate_explicit_token` | New accepted local contract |
| `check_lock_height` | Existing verified integration |
| `check_lock_time` | Existing verified integration |
| `current_sequence` | Existing verified integration |
| `fe_add` | Existing verified integration |
| `fe_is_odd` | Existing verified integration |
| `fe_is_zero` | Existing verified integration |
| `fe_multiply` | New accepted local contract |
| `fe_negate` | Existing verified integration |
| `fe_normalize` | Existing verified integration |
| `fe_square` | New accepted local contract |
| `ge_negate` | Existing verified integration |
| `gej_infinity` | Existing verified integration |
| `gej_is_infinity` | Existing verified integration |
| `gej_negate` | Existing verified integration |
| `input_sequence` | Existing verified integration |
| `nonce_hash` | New accepted local contract |
| `num_inputs` | Existing verified integration |
| `num_outputs` | Existing verified integration |
| `outpoint_hash` | New accepted local contract |
| `scalar_add` | Existing verified integration |
| `scalar_is_zero` | Existing verified integration |
| `scalar_multiply` | Existing verified integration |
| `scalar_negate` | Existing verified integration |
| `scalar_normalize` | Existing verified integration |
| `scalar_square` | Existing verified integration |
| `tx_is_final` | Existing verified integration |
| `version` | Existing verified integration |
| `calculate_issuance_entropy` | New accepted local contract |
| `fe_multiply_beta` | New accepted local contract |

## Scope and remaining obligations

- Every entry is a local Clight implementation-to-canonical-program contract,
  with its declared frame/environment preconditions. The target is LP64 Linux.
- The seven new Elements results retain `memcpy_model` and concrete initialized
  SHA dispatch/counter facts. They do not prove the linked libc implementation
  or general caller startup. Beta multiplication retains `beta_initialized`.
- The main multiply and square proofs are promoted. The independently checked
  parallel proofs remain an alternative archive, as requested.
- The Elements SHA proof copies name the actual Elements AST explicitly. They
  do not identify the ordinary SHA translation unit with the Elements program.
- Shared frame/evaluator admissibility and exhaustive inherited canonical
  fidelity review remain open; see `JET_INHERITED_REVIEW.md`.
- The remaining 89 header declarations have no registered final contract.
  Cached Bitcoin hashes and SHA startup helpers are support until their raw-data
  and operational boundaries meet the public coverage requirements.

## Recovered canonical boundaries

The calculation ports retain the literal hash-block programs: issuance entropy
uses the double-SHA outpoint digest plus the contract word; asset and token
calculations use the entropy word and the original zero/explicit/confidential
suffix block. The existing typed byte/word bridges preserve the index ordering,
SHA padding and word widths.

`asset_amount_hash` preserves the Haskell asset/amount branch order, prefixes
0x0a/0x0b and 0x08/0x09, explicit prefix 0x01, and the distinct 32/8-byte payloads.
`nonce_hash` retains absence/explicit/even/odd prefixes 0/1/2/3. `outpoint_hash`
retains the optional parent-chain hash followed by the 32-byte hash and four-byte
index. Each is a complete context-update success/failure contract over the
original C body; the literal ports and framing/global predicates are included
in the reviewed definition snapshots. These are scoped source/contract reviews,
not a verified Haskell compiler or a claim of completing inherited fidelity.

## Proof preservation and verification

Every jet module, including the former regression-only modules, is built and
recursively kernel-checked. Derived trees and known failing support experiments
remain archived outside the active build. Original upstream secp/modinv sources
retain their separate full-Coq build; they are not additional registrations.

The cleanup removes the fixed recursive source-reference gate, receipt metadata,
archive integrity machinery, obsolete run journals and byte-identical source
copies. Every active proof, reviewed snapshot and registration is unchanged;
every distinct archived Coq source and historical patch remains available.
The remaining literal correspondence checks and production source pins still
run. Removing the fixed reference loses its supplementary textual-drift check;
it does not prove any additional correspondence.

Full `bash Coq/check-jets.sh --accept` passed on cleanup source revision
`e7170ff9a83e3ccd0efd060e57854faa7944be4b`: 1,550 C modules built and
recursively kernel-checked, 1,305 assumption snapshots and 1,367 contract/definition
snapshots matched, negative fixtures passed, and all five pinned ASTs regenerated
identically. The 7,223 public result profiles and fifteen-entry inherited kernel
axiom allowlist are unchanged. No unsafe kernel category was enabled.

Both archived parallel multiplication/square endpoints also compiled in a fresh
external tree and passed recursive kernel checking with the same inherited
axiom allowlist. Reproduce that check with:

```sh
bash proof-work/fe-multiply-parallel/verify.sh /tmp/parallel-field-check
```

The Nix source filters now retain the review helper directories, snapshots,
project variants and required source/configuration inputs. Reconstructing their
filtered payloads preserved the complete audit fingerprint, and all source and
mutation checks passed against those isolated payloads. A full Nix derivation
was not run locally because Nix was unavailable.

The earlier focused `--accept --jets=simplicity_verify` test at `23adcc78`
verified that an unrelated listed, failing module does not block the selected
closure. Cleanup does not change closure selection or any selected proof.

Git preserves the original candidates and recovery history; see
`../../proof-work/README.md`. Current acceptance uses the commit and reproducible
commands, with run output outside the repository. Acceptance establishes the
local contracts and conditions above; the remaining 89 declarations and shared
evaluator/startup and inherited-fidelity obligations remain open.

## Subsequent completion: `gej_rescale`

`C.jet_secp_rescale_local.gej_rescale_literal_local_spec` proves the original
public C jet against the literal Haskell rescale/cube/zinv program for all four
Word256 inputs, including zero scale and arbitrary coordinates. It derives
the actual allocation, source-frame copy, readers, helper, writer, return and
frees under the existing `secp_jet_local_spec`; no curve/nonzero, startup or
libc-model premise is added. Its six assumptions are inherited Coq/CompCert
assumptions, with no new axioms. The selected multiply/square registrations
are unchanged.

Reproduce its acceptance with the declared Coq 8.17.1 toolchain:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_rescale
```

This checks the 291-module dependency closure, reviewed assumptions/contracts,
global source/mutation checks (including the new literal correspondence check)
and all five regenerated C ASTs. It passed without updating expectations or
changing production C, the frozen specifications, API contracts or generation
settings. This scoped result does not close the repository-wide obligations
listed above.

## SHA block boundary

`C.jet_sha_block_literal_local.sha_256_block_literal_local_spec` executes the
original SHA-unit jet for every Word256 state and Word512 block, against the
literal canonical block tree. The word-wiring bridges are closed equalities
in every Core algebra; the literal-add semantic bridge reuses the checked
adder adapter. The source gate compares the Core trees, 64 round constants
and word/bit dependencies, with 86 rejected mutations.

The local contract retains `sha_dispatch_ok`, requiring the initialized
portable compression function. Supporting startup and caller-lifecycle
theorems establish and preserve that state from the program's actual initial
memory through owned memory operations and verified jet calls. They do not
cover arbitrary externally installed dispatch callbacks, nor discharge the
general evaluator/caller obligations above. No libc model is required.

Reproduce scoped acceptance with the declared Coq 8.17.1 toolchain:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block
```

This passed the 264-module kernel closure, reviewed assumption/contract
comparisons, global source/mutation checks, negative tests and all five AST
regenerations, with unchanged audited inputs and no expectation updates.

The six local and eight startup/lifecycle assumptions are inherited; there
are no new project axioms. The selected field multiply/square endpoints remain
unchanged. This new registration does not assert a fresh full 432-entry audit.

## SHA context-add family

The ten `sha_256_ctx_8_add_{1,2,4,8,16,32,64,128,256,512}` entries select the
complete `sha_jet_partial_local_spec` theorems in `jet_sha_ctx8_literal_local.v`.
They prove execution of the actual SHA-unit public C functions against the
literal canonical assertion programs: successful results, false returns for
assertion failures, and the declared memory/frame properties. No input counter,
buffer length or failure case is excluded. All retain `memcpy_model` and
`sha_globals_ok`; they do not prove the linked libc implementation.

One shared program equality handles every byte-vector depth. The block
bridge is lifted to option semantics rather than repeating compression
proofs. The existing startup adapter gives ten stronger state-preserving
contracts, starting from the actual initialized program through the covered
caller lifecycle; arbitrary external dispatch replacements remain unproved.
The local theorems inherit six assumptions, startup variants eight, with no
new axioms. The source gate checks the canonical trees, buffer/increment/count
and assertion dependencies, recursion, all ten catalog/type/contract mappings,
and twenty context mutations (in addition to the block tests).

Reproduce family-scoped acceptance under the declared Coq 8.17.1 baseline:

```sh
sha_ctx_jets=$(printf 'simplicity_sha_256_ctx_8_add_%s,' 1 2 4 8 16 32 64 128 256 512)
bash Coq/check-jets.sh --accept --jets="${sha_ctx_jets%,}"
```

This passed the 265-module recursive kernel check, reviewed assumption and
contract comparisons, global source/mutation checks, negative tests and all
five AST regenerations. Audited inputs stayed unchanged and no expectations
were updated during acceptance.

These are ten conditional local-contract registrations, not a fresh full
442-entry acceptance audit or completion of the shared obligations above.

## SHA buffer-add and finalization

The selected complete local contracts are in `jet_sha_buffer_literal_local.v`
and `jet_sha_finalize_literal_local.v`. They execute the original public C
functions against the literal canonical assertion programs, including every
counter, buffer length, and assertion-failure case. They retain `memcpy_model`
and `sha_globals_ok`; they do not prove the linked libc implementation or
arbitrary externally installed dispatch callbacks. Startup variants reuse the
existing invariant and its preservation through the covered caller lifecycle.

The buffer bridge retains the empty-buffer count assertion and reuses the
one-byte/vector bridges. Finalization checks then clears the counter for
padding, assembles the padded block and original bit length, and calls the
literal block program. Constant shift/add wiring, padding stages and buffer
flags have closed program-equality proofs; option-semantic bridges reuse the
existing block bridge. The source gate compares the actual canonical trees
and their dependencies, with 24 additional rejected mutations.

The two local theorems inherit six assumptions and startup variants eight,
with no new project axioms. Reproduce acceptance under Coq 8.17.1:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize
```

This passed the 276-module recursive kernel check, reviewed assumptions and
contracts, global source/mutation checks, negative tests and all five AST
regenerations. Audited inputs stayed unchanged and no expectations were
updated during acceptance.

These are conditional local-contract registrations, not a fresh full
444-entry audit or closure of the shared evaluator/libc/fidelity obligations.

## TapData initializer and closed SHA program bridges

`jet_tapdata_literal_local.v` composes the original public C initializer with
the canonical `tapdataInit` program. Its local contract retains `memcpy_model`
and both `sha_globals_ok` and `sha_tag_ok`. Its startup variant reuses the
existing initialized portable-dispatch lifecycle; arbitrary externally
installed callbacks are not covered. The local theorem inherits six library
assumptions and the startup variant eight; neither adds a project axiom.

The scribed prefix is derived by `jet_tapdata_host_recipe.v`, a port of the
fixed two-block recipe in the vendored `Digest/Pure/SHA.hs`. Closed Coq
computations establish its tag bytes, padding, block lengths, digest and
prefix. The source check covers encoding, schedule, round constants and
complete public contracts, rejecting 131 additional mutations. This is
source-reviewed correspondence for the fixed host computation, not a formal
interpreter or general correctness theorem for Haskell's binary decoders.

The shared positive-depth adder bridge is now a reflexive equality in every
Core algebra. Consequently the SHA block, option, context-add, buffer-add and
finalizer program bridges no longer need functional extensionality. Existing
public C theorem types and programs are unchanged.

Scoped acceptance passed for TapData and all thirteen affected SHA jets:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block,simplicity_sha_256_ctx_8_add_1,simplicity_sha_256_ctx_8_add_2,simplicity_sha_256_ctx_8_add_4,simplicity_sha_256_ctx_8_add_8,simplicity_sha_256_ctx_8_add_16,simplicity_sha_256_ctx_8_add_32,simplicity_sha_256_ctx_8_add_64,simplicity_sha_256_ctx_8_add_128,simplicity_sha_256_ctx_8_add_256,simplicity_sha_256_ctx_8_add_512,simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize,simplicity_tapdata_init
```

The run passed the default recursive kernel check on 281 modules, assumption
comparisons for 176 modules, contract comparisons for 189 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
No audited inputs changed during the run and no expectations were updated.

This does not assert a fresh full 445-entry audit or closure of the remaining
shared evaluator, libc and fidelity obligations.

## Bitcoin pure builders and context hashes

The registry selects the complete original-C local contracts in
`jet_bitcoin_taproot_literal_local.v` for `build_tapleaf_simplicity` and
`build_tapbranch`, and `jet_bitcoin_ctx_hash_literal_local.v` for
`outpoint_hash` and `annex_hash`. All four retain `memcpy_model` and initialized
SHA state; the builders also require their original static tag state. Startup
variants reuse the actual initialized portable-dispatch lifecycle and preserve
its invariant. Arbitrarily installed compression callbacks are not covered.
These four contracts add no logical transaction-environment or cached-hash
premise. They are not proofs of the linked libc or general evaluator/caller.

The tag prefixes reuse the fixed host SHA port and the general formal
`haskell_hash_word256` decoding bridge. Closed computations establish block
lengths, serialization and both fixed prefixes. Closed Core-algebra equalities
connect the builders to their earlier C-proof targets; closed option-semantic
equalities connect the context hashes, covering every counter and optional
input, including assertion failure. This does not claim a general Haskell
binary-decoder/cryptographic-library correctness theorem.

The shared source gate follows actual library projections and compares the
complete canonical shift/order/padding and context-assertion trees. It rejects
27 new builder mutations and 14 context-hash mutations. All twelve new bridge
lemmas are closed; each local C theorem inherits six library assumptions and
each startup theorem eight, with no new project axioms.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_build_tapleaf_simplicity,simplicity_bitcoin_build_tapbranch,simplicity_bitcoin_outpoint_hash,simplicity_bitcoin_annex_hash
```

This passed the default recursive kernel check on 292 modules, assumption
comparisons for 186 modules, contract comparisons for 200 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 449-entry audit or discharge of the remaining
shared evaluator, libc, startup/caller and inherited fidelity obligations.

## Primitive-bearing SHA and Bitcoin tappath hash

The context-add, buffer-add and finalizer bridges now also hold in every
assertion algebra. Their existing option interfaces, program definitions and
public C theorem types are unchanged. `jet_sha_hash_words_literal.v` composes
these closed equalities into the canonical initializer, early-stopping loop
and array-hash program. `jet_bitcoin_tappath_hash_literal.v` instantiates the
program with the existing Tappath primitive and composes the original complete
C getter proof. All ten new program bridges are closed; the C theorem inherits
six library assumptions and adds no libc-model premise.

The exact environment/cache relation is still
`hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176`, with
the existing separation and frame contract. This proves the cached getter,
not the caller's cache construction. It retains the formal environment and
its path bound of 128 entries, matching the real C taproot builder's
well-formedness guard. It does not assert equivalence on arbitrary fabricated
overlong environments, nor resolve the inherited Bitcoin-domain discrepancies
in `JET_BITCOIN_MODEL_MISMATCHES.md`.

The existing source checker follows actual library projections, initialization,
loop termination/counter width, primitive selection and interpretation, and
the complete final C contract, rejecting 25 additional mutations. Host
interpreter correspondence is source-reviewed, not a general Haskell
interpreter correctness theorem.

Ordinary scoped acceptance passed for tappath hash and the fourteen affected
context-add/buffer/finalizer and Bitcoin context-hash consumers:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_ctx_8_add_1,simplicity_sha_256_ctx_8_add_2,simplicity_sha_256_ctx_8_add_4,simplicity_sha_256_ctx_8_add_8,simplicity_sha_256_ctx_8_add_16,simplicity_sha_256_ctx_8_add_32,simplicity_sha_256_ctx_8_add_64,simplicity_sha_256_ctx_8_add_128,simplicity_sha_256_ctx_8_add_256,simplicity_sha_256_ctx_8_add_512,simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize,simplicity_bitcoin_outpoint_hash,simplicity_bitcoin_annex_hash,simplicity_bitcoin_tappath_hash
```

This passed the default recursive kernel check on 315 modules, assumption
comparisons for 194 modules, contract comparisons for 211 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 450-entry audit or discharge of the remaining
shared evaluator, libc, startup/caller and inherited fidelity obligations.

## Bitcoin script and sequence array hashes

`jet_bitcoin_array_hash_literal.v` connects the canonical output-scripts,
input-scripts, input-sequences and input-scriptSigs hash programs to the original
complete C getter proofs. Its shared equality holds for every indexed primitive
and primitive algebra. The specializations retain 32-bit indices, 32-byte hash
elements or 4-byte sequence elements, initialization, early termination and
finalization. No prior execution theorem or program definition is changed.

The exact `application_jet_local_spec_sep` framing and `hash_getter_rep`
relations are retained, at transaction offsets 48, 176, 240 and 304. Each C
endpoint inherits six library assumptions and adds no libc premise. The shared
program equality is closed. Normal compilation, recursive kernel checking with
supported VM conversion and reviewed snapshot comparisons passed. The source
checker validates the four full canonical programs and selected primitive
projections, rejecting 34 additional mutations; this is not a general Haskell
interpreter theorem.

These are cached-getter contracts, not proofs of caller cache construction or
full Haskell-to-Coq environment-domain agreement. The frozen-domain differences
in `JET_BITCOIN_MODEL_MISMATCHES.md` remain unresolved. The extended input-script
and scriptSig hash lists remain abstract logical fields; this batch does not
establish them from raw caller scripts.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_scripts_hash,simplicity_bitcoin_input_scripts_hash,simplicity_bitcoin_input_sequences_hash,simplicity_bitcoin_input_script_sigs_hash
```

This passed the default recursive kernel check on 241 modules, assumption
comparisons for 126 modules, contract comparisons for 143 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 454-entry audit or discharge of the shared
evaluator, libc, startup/caller, domain and inherited-fidelity obligations.

## Raw interpretation of five composed Bitcoin hash programs

`jet_bitcoin_raw_program.v` restores the preserved generic raw-program bridge
unchanged. Its algebra keeps the same primitive signature, uses the frozen
Bitcoin interpretation for base primitives, and computes extended script and
scriptSig hashes from raw bytes. A relation covering all Core combinators,
assertions and failure transports every parametric program through the existing
`project_raw_environment` projection.

`jet_bitcoin_hash_raw_literal.v` composes this result with the accepted literal
output-scripts, input-scripts, input-sequences, input-scriptSigs and tappath
programs and complete C contracts. The generic helper's parametricity and C
execution premises are discharged by the concrete final proofs. The registry
now selects these five raw variants; this is a semantic-boundary strengthening,
not additional declared-jet coverage.

The underlying cache/frame relation is retained through `raw_env_rep`, with
its existing path bound. No actual C caller cache construction is proved by
this batch. The frozen base domain and reported Bitcoin mismatches are
unchanged. This is not a general Haskell interpreter correctness theorem.

Both modules compile and reviewed snapshots match. The direct primitive
projection and literal-parametricity lemmas are closed; the general relation
and program-projection lemmas inherit functional extensionality. All five C
endpoints retain the same six inherited library assumptions, without an added
libc or execution/output premise. Source checks reject 22 further mutations of
raw semantics, representation boundaries and complete C contracts.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_scripts_hash,simplicity_bitcoin_input_scripts_hash,simplicity_bitcoin_input_sequences_hash,simplicity_bitcoin_input_script_sigs_hash,simplicity_bitcoin_tappath_hash
```

This passed the default recursive kernel check on 272 modules, assumption
comparisons for 143 modules, contract comparisons for 166 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
Audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 454-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Bitcoin tapleaf and tap-environment hash getters

`jet_bitcoin_tap_hash_literal.v` adapts the preserved tapleaf program tree to
the accepted fixed-tag host recipe, literal tagged-context initialization and
algebra-general SHA bridges. It supplies the full canonical `tapleafHash` and
`tapEnvHash` trees, equality in every primitive algebra, and complete original-C
contracts in both abstract and raw interpretations. The registry selects the
two raw endpoints.

The cache/frame relations are unchanged: `hash_getter_rep tapleaf_hash_of 8 8 176`
and `hash_getter_rep tap_env_hash_of 8 72 176`, lifted through `raw_env_rep`.
The final theorems discharge their shared helper's program-parametricity and
execution obligations using the existing proofs. They add no libc or
execution/output premise. The three program-equality and two parametricity
lemmas are closed; all four C variants inherit the same six library assumptions.

The tagged-context adapter is general in an already supplied prefix. Its use
here instantiates the previously checked fixed `TapLeaf` host recipe; it is not
an interpreter claim for arbitrary tags. The source checker compares the actual
explicit algebra trees with the complete canonical programs, checks library
dispatch, initialization and primitive/raw projections, and protects all four
C boundaries, rejecting 22 further mutations. Normal compilation and reviewed
snapshot comparisons passed; these are not acceptance by themselves.

Actual caller cache construction, the existing path bound and frozen-domain
differences remain open as before. No production C, canonical program or
primitive signature/domain has been changed.

Ordinary scoped acceptance passed: 282 kernel-checked modules, matching
assumption records for 153 modules and contract records for 176 modules,
negative tests and all five AST regenerations. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_tapleaf_hash,simplicity_bitcoin_tap_env_hash
```

This does not assert a fresh full 456-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Bitcoin input outpoint, annex and combined-input hash getters

`jet_bitcoin_inputs_hash_literal.v` reuses the original element-loop body and
the accepted literal SHA/context programs to port the complete canonical
`inputOutpointsHash`, `inputAnnexesHash` and `inputsHash` programs. It generalizes
the outpoint/annex append equalities to every assertion algebra, without changing
the existing option-only APIs. The shared element adapter and all three whole
program equalities/parametricity lemmas are closed.

Six complete C contracts compose the existing getter executions in abstract and
raw primitive interpretations. The registry selects the three raw endpoints.
The cache/frame relations remain `hash_getter_rep ... 0 <offset> 432`, at offsets
112, 272 and 336, respectively, lifted through `raw_env_rep`. They add no libc,
execution or output premise and retain the same six inherited library
assumptions. Caller cache construction, the existing raw path bound and the
frozen-domain discrepancies remain open.

Normal compilation and reviewed snapshot comparisons passed for all fifteen
public theorem records and four new program definitions. The existing source
checker compares complete loop/composition trees, canonical library dispatch,
primitive/raw interpretations and all six C boundaries, rejecting 33 further
mutations. In particular, it distinguishes an absent input (stop) from a
present input with no annex (continue, appending byte zero).

Ordinary scoped acceptance passed: 280 kernel-checked modules, matching
assumption records for 151 modules and contract records for 174 modules,
negative tests and all five AST regenerations. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_input_outpoints_hash,simplicity_bitcoin_input_annexes_hash,simplicity_bitcoin_inputs_hash
```

This does not assert a fresh full 459-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Computing Bitcoin input hash and seven Elements array hashes

`jet_bitcoin_input_hash_literal.v` composes the complete original C computing
jet with the canonical primitive-bearing `inputHash` program, including its
assertions and absent-input/absent-annex/present-annex cases. The registry
selects the raw interpretation. Its three bridges are closed; both C variants
retain six inherited library assumptions and the existing explicit
`memcpy_model` premise. The existing `input_hash_rep` relation, including SHA
global readiness and environment/output separation, is unchanged.

`jet_sha_hash_words_reader.v` and `jet_elements_words_hash_program.v` restore
the preserved generic option-Reader semantics and seven complete Elements C
cache getters without source changes. They reuse the existing SHA traversal
and absorption/finalization results; there is no artificial Bitcoin environment
or assumed hash/execution oracle.

`jet_elements_array_hash_literal.v` connects these getters to the shared
literal SHA programs. The registry selects output scripts/range proofs/
surjection proofs, input scripts/sequences/scriptSigs, and tappath. Both generic
bridges are closed; all seven C contracts retain the same six inherited
assumptions and no extra libc premise. Their cache/frame relations remain
`hash_getter_rep` at the original offsets (88, 120, 152, 280, 344 and 408 in a
760-byte transaction; 40 in the 176-byte taproot environment).

Normal compilation and reviewed snapshot comparisons passed across the four
new modules: 50 theorem records and 20 definitions. The existing source checker
compares the complete single-input tree/boundaries and the seven Elements
streams, raw primitive/proof views and C boundaries, rejecting 27 and 51 further
mutations, respectively. The exact conditional-count test now expects 129,
including the computing Bitcoin jet's existing libc premise; rejection of
substituted models or missing/extra premises remains required.

Caller environment/cache construction, persistent SHA startup, existing model
domain/path bounds, libc implementation and general host-library fidelity are
not discharged here. No production C, original specification or generation
configuration changed.

Ordinary scoped acceptance passed: 373 kernel-checked modules, 242 assumption
records and 266 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_input_hash,simplicity_output_scripts_hash,simplicity_output_range_proofs_hash,simplicity_output_surjection_proofs_hash,simplicity_input_scripts_hash,simplicity_input_sequences_hash,simplicity_input_script_sigs_hash,simplicity_tappath_hash
```

This does not assert a fresh full 467-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements input and taproot hash getters

`jet_elements_inputs_hash_literal.v` composes three complete original C cache
getters with the canonical primitive-bearing input-outpoints, input-annexes and
combined-input hash programs. Both outpoint primitive lookups and early exits,
the absent/present-annex encoding and the full SHA composition are retained.
Nine bridges are closed. The C contracts keep `hash_getter_rep` at offsets
216, 376 and 440 in the 760-byte transaction.

`jet_elements_tap_hash_literal.v` composes the complete original tapleaf and
tap-environment getters with canonical programs using TapleafVersion,
ScriptCMR, Tappath and InternalKey primitives. Seven bridges are closed,
including fixed host serialization and the exact `"TapLeaf/elements"` tag.
Native `Schnorr.PubKey` contains `Word256`, not a field element. The C contracts
keep offsets 8 and 72 in the 176-byte taproot environment.

All five final contracts have the same six inherited library assumptions and
no extra libc premise. Six preserved support modules were restored unchanged;
the generic Reader/loop results and existing complete C getter proofs are
reused, without an assumed execution or arbitrary cached-hash primitive.
Normal compilation, reviewed snapshots for 55 theorem records and 32
definitions, and comparisons without update flags pass. The existing source
checker rejects 36 additional input-tree/boundary mutations and 32
taproot/tag/native-key/boundary mutations. Existing negative tests remain
unchanged.

Caller cache construction, the existing model/domain/path bounds and general
host-library fidelity remain separate obligations. No production C, original
specification or generation configuration changed.

Ordinary scoped acceptance passed: 324 kernel-checked modules, 193 assumption
records and 217 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_input_outpoints_hash,simplicity_input_annexes_hash,simplicity_inputs_hash,simplicity_tapleaf_hash,simplicity_tap_env_hash
```

This does not assert a fresh full 472-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements issuance-proof, nonce and amount hash getters

Three adapters connect complete original C cache getters to the canonical
primitive-bearing programs. `jet_elements_issuance_proofs_hash_literal.v`
retains both primitive lookups and early exits and reuses the existing closed
asset/token proof-view lemmas. `jet_elements_nonces_hash_literal.v` distinguishes
absent output from absent nonce and reuses the native Word256 encoder bridge.
`jet_elements_amounts_hash_literal.v` shares the canonical asset/amount
serializers and primitive-pair loop between input and output hashes. Prefixes
0/1/2/3, 10/11 and 8/9 and the explicit amount's 8-byte payload are retained;
there is no new field-element restriction on native nonce words.

Six preserved support modules are restored without source changes. The generic
Reader loop, prefix/payload absorber and existing complete C getter proofs are
reused, not replaced by execution/hash oracles. The four final contracts keep
`hash_getter_rep` at offsets 536, 56, 24 and 248 in the 760-byte transaction.
All four have the same six inherited library assumptions and no extra libc
premise; all 17 adapter bridges are closed.

Normal compilation passes after rebuilding unchanged stale dependencies with
the pinned toolchain. Reviewed snapshots cover 65 theorem records and 52
definitions across nine modules; comparisons without update flags pass. The
existing source checker rejects 19 issuance-loop, 20 nonce and 26 amount-hash
mutations, reusing the mandatory primitive/native-encoding/pair-routing guards.
Existing gate negative tests remain unchanged.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. No production C,
original specification, API or generation configuration changed.

Ordinary scoped acceptance passed: 367 kernel-checked modules, 235 assumption
records and 260 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_range_proofs_hash,simplicity_output_nonces_hash,simplicity_output_amounts_hash,simplicity_input_amounts_hash
```

This does not assert a fresh full 476-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements composite hashes, blinding entropy and issuance status

Ten preserved support modules are restored without source changes; two new
adapters connect complete original C getters to the shared literal programs.
`jet_elements_composite_hash_literal.v` reuses one fixed-vector SHA skeleton
for the canonical four-component outputs hash and two-component input-UTXO
hash. `jet_elements_blinding_entropy_literal.v` retains the three primitive
lookups, optional/new/reissuance routing and actual `Arith.one word8` program,
including its reviewed padding dependencies. The eight adapter bridges are
closed. The three full C contracts keep the original `hash_getter_rep` at
transaction offsets 184, 312 and 568 in the 760-byte structure.

The preserved `jet_elements_issuance_status_local.v` is already a literal
primitive-program endpoint for the original `simplicity_issuance`. It covers
every Word32 index and out-of-range/no-issuance/new/reissuance results. Its
initial relation represents only pointers/count and the enum at input offset
528, with stride 544 and count offset 696. It has no hash-cache, execution,
desired-output, nonzero-issuance or initialized-output premise. The actual
enum reload after the first payload write is preserved by its derived effect.
It still requires valid separated frames and is not an overlapping-buffer API
claim or production caller-construction proof.

All four endpoints retain the same six inherited library assumptions and no
extra libc premise. Normal compilation and reviewed snapshot comparisons pass
for 55 theorem records and 43 definitions across twelve modules. The existing
source checker rejects 26 composite, 24 blinding-entropy and 17 issuance-status
mutations, including component reordering, replacing the one-word program,
reversed `flip match` branches and vacuous final contracts. Existing gate
negative tests remain unchanged.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. No production C,
original specification, API or generation configuration changed.

Ordinary scoped acceptance passed: 362 kernel-checked modules, 231 assumption
records and 255 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_outputs_hash,simplicity_input_utxos_hash,simplicity_issuance_blinding_entropy_hash,simplicity_issuance
```

This does not assert a fresh full 480-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Candidates: Elements computed issuance getters

Three preserved modules supply the complete original `issuance_entropy`,
`issuance_asset` and `issuance_token` getter executions. Two literal adapters
reuse the existing universal SHA-block and Haskell-word bridges. The new
outpoint program retains both compressions, the four-byte index reversal,
288-bit length and original second-block constant. The primitive programs
retain missing input, no issuance, new issuance and reissuance routing;
token selection still distinguishes confidential from explicit asset amounts.

The final contracts retain `application_jet_local_spec_sep` and the initial
`computed_issuance_hash_rep` at issuance-relative offsets 72, 168 and 200.
The actual enum load is at input offset 528, with stride 544 and count offset
696. Cache loads after output writes are derived from separation and effects.
No execution, desired-output, success, zero-output or issuance-kind premise
is added. The three C endpoints retain the same six inherited assumptions
and no extra libc premise. The sixteen new program bridges/parametricity
results are closed.

Normal compilation passes. Reviewed snapshots cover 39 theorem records and
37 definitions in five new modules; the existing calculation snapshots are
unchanged. The existing source checker rejects 35 further mutations of
constants, byte order, primitive routing, offsets and complete C contracts.
These candidates are not registered or accepted yet. Reproduce the required
ordinary scoped acceptance after registration:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_entropy,simplicity_issuance_asset,simplicity_issuance_token
```

The real Elements builder must still establish the cached-value relation.
Existing caller/domain/layout and host-library obligations remain; the
production C, original specifications, API and generation settings are fixed.
