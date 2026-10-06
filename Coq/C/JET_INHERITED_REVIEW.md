# Inherited-work review against the eight goal criteria

Status: **partially complete**. The initial assessment covers proof inputs at
`4888ca776165497ab440bd6083292b3facc5d533`; subsequent reviews below leave those
published proof inputs unchanged. It supersedes any interpretation of
"accepted consolidation" as a complete specification-fidelity review of every
inherited result. No new jet proof is developed or promoted in this assessment.

`JET_ACCEPTANCE.md` records successful verification of particular inputs and
reviewed changes. It is not a per-jet certificate that every unchanged inherited
specification, representation predicate and precondition was independently
compared with the canonical program. Compilation, stable snapshots and absence
of admitted proofs do not supply that missing evidence.

## Direct answer before further jet development

The inherited correction is **partially complete**, not fully complete and not
merely of unknown status. Concrete deviations have been corrected and scoped
verification/review evidence exists; other concrete memory-domain exclusions
remain pending, and the exhaustive review required by criteria 6–8 is unfinished.

For the registered inventory, the answer to "was every complete chain reviewed
without assuming execution/output, restricting legitimate inputs or weakening
conclusions?" is **not yet**. The 347 entries are previously accepted contracts,
not 347 independently recertified canonical-fidelity results. The evidence
matrix distinguishes completed local reviews from pending rows; even a local
review does not close unresolved shared memory-representation admissibility.

The following four classifications remain separate: corrected inherited
deviations; inherited declarations not yet fully reviewed; confirmed/suspected
pending deviations; and additional coverage/support unrelated to repairing the
earlier claims. Remaining fidelity review and corrections take priority over
new jet coverage.

## Corrected deviations and evidence

| Correction | Commit | Evidence and exact limit |
| --- | --- | --- |
| Restore original `copyBitsHelper`/external memcpy instead of the added `copyWords` implementation | `103334a712b92bea684d0d958cad016382693e69` | Production C and canonical Haskell match the pinned target. The only tracked C/Haskell difference is the cursor-copy regression test in `C/test.c`, outside the proof translation units. Four regenerated AST comparisons passed in the separate final acceptance. |
| Restore explicit libc premises and derive caller obligations | `103334a7` | `jet_memcpy_model.v:22` states validity, source loadbytes, destination Writable permissions, non-overlap, positive representable length and no wraparound. Actual calls use `EF_external "memcpy"`, three arguments, destination-pointer return and E0 trace. The builtin witness is auxiliary and does not prove libc. |
| Correct Bitcoin environment domain, fee direction and modular caches | `463a4297` | The Coq environment no longer excludes positive fees, zero outputs or high-bit Word64 amounts. Totals/fees use modular Word64 correspondence. `jet_bitcoin_value_domain.v` proves the domain bridges; final acceptance rebuilds the affected callers. |
| Correct primitive commitment identity | `35d1e347`, extended by `db7450b1` | Canonical names/types, including `lockTime`, are checked against the pinned Haskell interface. This checks identity; hash-cache correctness is a separate obligation. |
| Replace cache-only semantics at registered hash-getter boundaries with raw-data semantics | `db7450b1` | `jet_bitcoin_raw_env.v` and `jet_bitcoin_raw_jets.v` give independent hashes/projection and preserve lookup/annex failures. Supplied transaction-id correspondence remains an explicit initial representation requirement, not a claim that the C constructor verifies serialization. |
| Strengthen verification acceptance | `8730b302`, `bb66c0a9` | Separate candidate generation and acceptance, frozen input fingerprint, public types/definitions, complete module inventory and kernel/axiom checks. Negative fixtures reject impossible premises, weakened conclusions/definitions and inline escape hatches. This protects reviewed contracts; it does not retrospectively validate every inherited definition. |

The existing-statement comparison artifact
`/tmp/jet-existing-statement-review.json` covers **109 changed statements in nine
copy-family files**: 92 restored final libc premises, 12 helper premises and
five external-call/ABI adaptations. The recorded review preserves their output
and framing conclusions. That artifact is a scoped change comparison, not an
exhaustive canonical review of all public statements.

Verification receipts:

- Original-target consolidation: `/tmp/jet-consolidation-final-accept.log`,
  `accept_exit_status=0`, input SHA-256
  `6ab077ecd6bb173899701f63bfb966ee811e09618bc06df3879d8bc6ca4ee47f`.
- Reviewed canonical continuation: `/tmp/jet-next-canonical-final-accept.log`,
  `final_accept_exit_status=0`, input SHA-256
  `a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`.
- Latest published proof inputs: `/tmp/jet-secp-normalize-final-accept.log`,
  `final_accept_exit_status=0`, input SHA-256
  `5d01956807ea2f325ca099e65818f5e23d521e31ac994863c1f5fd09deeb6eae`.
  It includes four direct AST regenerations, 583 kernel modules and 3,534
  assumption records. These checks are verification evidence, distinct from
  the source-level fidelity evidence described for each reviewed family.
- This assessment reran `check-jet-source-target.py`: all 240 pinned inputs
  match. No proof/C/Haskell/generation input was edited.

## Eight-criterion assessment

| Goal criterion | Status | What remains |
| --- | --- | --- |
| 1. Fix target commit/configuration and compare implementation changes | Complete for the selected target | `e3b670103101108faa238df012676ff5d8b77cf9`, x86-64/Linux LP64, Coq 8.17.1, CompCert 3.14, VST 2.14 and pinned glibc headers. This does not cover every build configuration. |
| 2. Reverse the introduced copyWords implementation drift, preserving useful work | Complete | History/support preserved; original memcpy path restored. |
| 3. Preserve C and regenerate corresponding ASTs directly | Complete for the four proof translation units | Core, Bitcoin, SHA and secp AST comparisons passed. Elements lacks a corresponding accepted proof chain. |
| 4. Keep memcpy as EF_external and derive its call preconditions | Complete for the repaired callers | Libc implementation remains outside the proof; builtin equivalence is not substituted. |
| 5. Report conditional results explicitly | Complete in the current registry | 104 entries retain `memcpy_model`; 243 have no extra libc premise but retain initial representation contracts and inherited Coq/CompCert assumptions. |
| 6. Close real C -> Clight -> output representation -> canonical program | Partial | Documented complete chains exist for reviewed families. No exhaustive per-entry evidence matrix for all 347 entries has been completed. Experimental composed hashes and other unregistered results must not count merely by theorem name. |
| 7. Reuse mathematical/executor support without confusing it with final equivalence | Partial | Support is separated from the registry. The full inherited inventory still needs statement/definition/boundary classification; mathematical field/scalar results alone add no coverage. |
| 8. Review definitions, conclusions and hypotheses for fidelity | Partial | Actual changed statements and selected canonical families were reviewed. Unchanged snapshots cannot establish correctness of their baseline. Exhaustive review of all inherited contracts and their transitive semantic definitions remains required. |

## Inherited work whose review is not exhaustively demonstrated

The stopped experimental branch adds 126 Coq paths relative to `ebf17493`:
122 `.v` modules, two translation units and two regeneration scripts. By filename
family the modules comprise 53 SHA, 40 Bitcoin, six secp, ten symbolic-executor
and 13 other modules. All are in the compiled/audited inventory after
consolidation; these counts are not counts of independently reviewed canonical
equivalences.

The remaining review must enumerate actual declarations and their transitive
definitions, not just these filename groups. In particular:

- **SHA:** review canonical ctx8/buffer/finalize/tagged programs and every
  `sha_globals_ok` boundary. Isolated initializer/preservation helpers do not
  yet derive that invariant throughout all real caller lifecycles.
- **Composed Bitcoin hashes:** review `input_hash`, `input_utxo_hash`,
  `output_hash`, `outpoint_hash`, transaction/sig-all hashes and tap construction
  against raw primitives, exact serialization/padding, globals and failure
  behavior. Literal-port inspection of selected programs is not the full chain.
- **secp support:** classify field/integer/byte-limb helper premises and show
  which are discharged by a public jet. The completed `fe_normalize` chain does
  not certify every other field helper or jet.
- **Symbolic execution and intervals:** inspect soundness/oracle contracts and
  their downstream instantiations for event, invariant, representation and
  range premises. Kernel checking establishes the stated lemmas, not that an
  arbitrary consumer satisfies those premises.
- **Every registered jet:** attach a source-level canonical binding/type/domain
  comparison, expanded final conclusion/preconditions and the actual derivation
  of intermediate execution/output facts. Existing family reviews should be
  reused, but there is no completed one-row-per-entry cross-reference yet.

This is a gap in the demonstrated review scope, not evidence that every module
in those groups contains a defect. No unregistered experimental result is
promoted by this assessment.

## Known pending obligations versus suspected deviations

**Known proof obligations:** derive SHA startup/global preservation through
complete callers; transport composed Bitcoin hash contracts to canonical raw
semantics; complete the remaining public secp/Elements chains. The first two
are necessary to justify inherited claims before promoting them. `sha_globals_ok`
and cache/environment relations must not become hidden execution/output premises.

**Trust boundaries, not silently discharged obligations:** the actual libc
implementation under `memcpy_model`; the C constructor's caller-supplied txid;
initial valid frame/environment representations. Their legitimacy and domain
must be checked at each public theorem, and reported explicitly.

**Suspected/unresolved fidelity risks:** baseline canonical dispatch/ports,
logical environment restrictions, representation predicates that might encode
the desired answer, failure conclusions and strengthened preconditions in parts
without a complete source review. These are review questions, not confirmed
new defects. Snapshot stability cannot dismiss them.

`JET_SHARED_MEMORY_REVIEW.md` additionally validates a concrete shared-predicate
restriction: frame_base_valid excludes an object whose exclusive end is
max_unsigned+1 even though its field pointers, accessible bytes and actual
Clight field expression are valid. This is a semantic-domain exclusion, not a
proved wrong jet output or proved reachable Linux allocation. The candidate
wider bound is being verified in a separate attached worktree; no proof or
snapshot from it is yet accepted or published. The general memory-contract
admissibility review remains open for every affected local contract.

`JET_SHARED_BLOCK_REVIEW.md` validates another concrete exclusion: the original
writeBit executes correctly with a frame and its data in disjoint byte ranges
of a single 24-byte allocation, yet write_frame_at rejects it by bf <> bw.
The actual call, cursor and output are derived from constructed initial memory.
A generic writer proof using byte-range separation also passes compilation and
kernel checking. These are correction-support/diagnostic results, not new jet
coverage or a completed generalization of all public memory contracts.

The same report now records seven further compiled/kernel-checked correction
support results: an initial predicate implied by every old write_frame_at,
total original writeBit execution with all original conclusions, preservation
of the remaining writable frame and a 24-byte shared-block instance for
arbitrary initial word/Boolean values. Intermediate store facts are derived at
the total boundary. The public predicates and downstream contracts are still
unchanged, and their repair remains necessary; none of this adds jet coverage.

Subsequent support extends this to complete byte sequences and the actual
write8s pointer/count loop, retaining every original canonical-output and
framing conclusion. Twenty results in seven isolated modules pass compilation
and independent kernel checking; input-array separation remains explicit and
still needs scope review. Actual public-predicate/writer adaptation has begun
in a separate candidate worktree. It is not integrated or published, and full
consumer rebuilding/review/acceptance remains required.

The first four private atomic range-separation commits are:
`4e3c738f` (bit/byte writers), `0414f7d5` (wide/carry writes), `02894d42`
(canonical byte sequences and actual write8s), and `ee415533` (context/one8
transports). Sixteen changed modules have scoped rebuild and independent kernel
checks. Reviewed total statements/conclusions remain unchanged; intermediate
block-disequality premises are replaced by separation of the actual byte ranges.
The context/one8 transport changes alter proof scripts only. These commits are
not integrated or published. Whole-consumer rebuilding, snapshot/type/definition/
axiom review and independent full acceptance are still pending, so this is
verified correction progress rather than a completed published repair. It adds
zero registered jets. See `JET_SHARED_BLOCK_REVIEW.md` for receipts and limits.

Four subsequent private commits (`9399ab14`, `d8f26a0f`, `2217368e`, `c8bb852e`)
extend this to 26 scoped rebuilt/kernel-checked modules: write32s, actual
skipBits padding and existing add/increment layouts at all four widths. Their
existing total types and definitions remain unchanged. The zero-length padding
case derives same-value-store preservation even with exact alias, rather than
adding an unused-data separation premise. Additional consumer transports are
being rebuilt, outside those completed receipts. Full acceptance and publication
of the range candidate remain pending.

The separate endpoint candidate audit has now completed with exit 0: all four
ASTs match, all 3,534 per-theorem assumption records and library axiom sets are
unchanged, and only the intended exclusive-end definition differs. Actual
source/snapshot comparison is recorded in
`/tmp/jet-frame-memory-snapshot-review.json`. Independent full acceptance is
running; the endpoint repair is not yet accepted, integrated or published.

**Confirmed documentation overstatement corrected here:** earlier "accepted"
and "completed consolidation review" wording could be read as completion of
all eight criteria. Only the scoped verification/reviews were complete. The
target document also retained the older 346-entry count; the published registry
is 347 entries. Neither change creates a new proof or enlarges coverage.

## New coverage and auxiliary work, separate from inherited corrections

`fe71729c` registered 27 reviewed existing contracts (12 libc-conditional
full shifts and 15 Bitcoin contracts), with raw annex support in `22c7d711`.
This reused inherited work; it is not 27 newly written whole-jet proofs.

`bc4f2837` added the complete original-C canonical `fe_normalize` proof and
`4888ca77` its receipt. The new reader/writer/lifecycle bridge enlarged coverage
by one. It is useful new work, separate from repairing memcpy or Bitcoin domains.

The subsequent `fe_is_odd`/`fe_is_zero` candidates and scalar/u128 helper work
are unpublished. The predicate candidate audit already in progress may finish,
but it will not be accepted or published before the inherited review takes
priority. Scalar helpers add no jet coverage; the latest overflow-flag scratch
file has a failed compilation and is not a verified result.

## Coverage interpretation and next work

The current **registered, previously accepted inventory** remains 347/533:
243 without an extra libc premise, 104 conditional and 186 unregistered
(59 core, 24 Bitcoin, 103 Elements). Two public secp declarations have no jet-node
registration and remain in the denominator. The 186 missing registrations are
not the number of pending fidelity reviews.

**It is not yet justified to certify, individually for every one of those 347
entries, all eight criteria solely from the available reports.** Do not relabel
the inventory as an exhaustively recertified fidelity count. Reclassification
of a particular entry must follow a concrete source/statement finding.

Next priority is a declaration-level evidence matrix for the inherited modules
and registered contracts, followed by source/definition/hypothesis review of its
unresolved rows and correction of concrete findings. New jet development and
promotion are deferred. Completion requires that matrix and its substantive
review, not another unchanged aggregate compilation.

## Evidence matrix started after this assessment

`JET_EQUIVALENCE_REVIEW_MATRIX.csv` now records every public C declaration and
its actual registered theorem. `JET_INHERITED_DECLARATIONS.csv` indexes the
122 inherited modules, including module namespaces, source locations/hashes and
all their individually audited public names. Their pending statuses are explicit;
enumeration is not completion of fidelity review.

`JET_BITCOIN_TIMELOCK_VALUE_REVIEW.md` adds a per-contract source/definition/
precondition/conclusion review of 12 existing TimeLock/totals/fee chains and
15 kernel-checked semantic boundary diagnostics. Initial cache correspondence
is retained and explained; transaction-constructor correctness is not claimed.
No new discrepancy or coverage increase is reported for this family. The full
inherited review remains partial.

`JET_BITCOIN_SIMPLE_GETTERS_REVIEW.md` adds six existing local chains: version,
lock_time, current_index, num_inputs, num_outputs and script_cmr. It reviews the
actual linked bodies/lifecycle, unsigned-word/hash encoding, literal firstFail
recursion, domains, initial representations and full output/framing conclusions.
Nine closed diagnostics and a general literal-search domain lemma pass complete
compilation and separate kernel checking. No new discrepancy or registration
is reported. Constructor establishment and general memory-contract admissibility
remain outside this local review.

`JET_BITCOIN_INDEXED_CURRENT_REVIEW.md` adds eight existing indexed/current
getter chains, including present/absent lookup, literal current assertions,
full-word values, outpoint order, helper transport and source-level comparison
of the actual canonical SHA primitive implementation. Eighteen closed examples
and a general max-index lemma pass complete compilation and independent kernel
checking. Constructor establishment and general memory-contract admissibility
remain open. No new coverage is reported, and this round has no path overlap
with the stopped experimental declaration inventory.

The current matrix has 26 reviewed local contracts, 36 prior family reviews,
one prior complete chain, 284 registered rows requiring further evidence
cross-reference and 186 missing final registrations. These are review statuses,
not a change to the 347/533 registered inventory. Next are the remaining
shared frame/address-contract admissibility and its endpoint repair, followed
by ten registered Bitcoin raw getters and SHA/composed-hash boundaries. None
of the local review statuses closes the shared-contract review globally.
