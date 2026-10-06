# Inherited-work review against the eight goal criteria

Status: **partially complete**. This assessment covers the published tree at
`4888ca776165497ab440bd6083292b3facc5d533`. It supersedes any interpretation of
"accepted consolidation" as a complete specification-fidelity review of every
inherited result. No new jet proof is developed or promoted in this assessment.

`JET_ACCEPTANCE.md` records successful verification of particular inputs and
reviewed changes. It is not a per-jet certificate that every unchanged inherited
specification, representation predicate and precondition was independently
compared with the canonical program. Compilation, stable snapshots and absence
of admitted proofs do not supply that missing evidence.

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
