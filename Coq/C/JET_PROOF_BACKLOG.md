# Proof consolidation and remaining obligations

Current consolidation preserves every useful source identified in the known
branches, worktrees and 84-file scratch inventory. Accepted sources remain in
the active Coq tree. Unaccepted corrections, candidate registrations, helper
sources and review witnesses are versioned in `../../proof-work/`, outside the
accepted build. Consolidation is source preservation, not proof acceptance.

The latest full-acceptance receipt covers **349/533**. Commit `cafb9b31`
registers two further canonical field predicates, bringing the current registry
to **349/533** (245 without an extra libc premise, 104 conditional on the
explicit original `memcpy_model`, 184 missing). Independent full acceptance of
this extension passes with exit 0 on 2026-10-09; its exact fingerprint and
completed checks are recorded in `JET_ACCEPTANCE.md`.
The inherited fidelity review is still
**partial**. `JET_INHERITED_REVIEW.md` is the authoritative eight-criterion
assessment; compilation, snapshots and absence of admissions do not complete it.

## Existing accepted correction and review evidence

Latest isolated negation progress: the complete `fe_negate_local_spec` candidate
now compiles, deriving the original public call's allocation/source copy,
read/negate/write/return/free lifecycle and canonical output/prefix/cursor/load
framing over arbitrary Word256 inputs. Five new modules are archived with
hashes in `../../proof-work/fe-negate/manifest.json`. Its printed final
assumptions are the six inherited execution assumptions, without an extra
libc premise. Combined-call kernel session 62934 passes; independent public
whole-chain kernel checking at the default stack ended with stack overflow;
the corrected 65520 KiB-stack run passes with exit 0 (10047), with 15 existing
library axioms and no unsafe kernel flags. The scoped negate wiring gate
passes and rejects 19 mutations. A scoped recursive-port gate now freezes
25 typed Coq declarations and six canonical Haskell regions, rejects 43
mutations and passes on accepted/reconciled-range sources. Remaining transitive
bit/arithmetic/type/encoding review is explicitly open in the canonical review.
Canonical source/negative
gate review, snapshots, full acceptance and integration remain pending; this
does not change accepted coverage. Older negation work-order notes below are
historical where superseded by this complete candidate.

The frame exclusive-end correction is accepted as `063e3b04`, and the exact
audited input fingerprint remains the one recorded in
`JET_CONSOLIDATION_2026-10-06.json`. `JET_SHARED_MEMORY_REVIEW.md` records its
definition/domain review. The production C, canonical Haskell, accepted ASTs,
public theorem statements, conclusions and assumption sets are unchanged by
this source-archive consolidation.

The original-C normalization result and its full public lifecycle are already
integrated. The scope of its canonical review is recorded in
`JET_FIDELITY_REVIEW.md` and `JET_ACCEPTANCE.md`.

Prior full-shift family review inspected the literal Haskell catalog and
recursive programs. The twelve `full_left/right_shift_64_{1,2,4,8,16,32}`
contracts retain actual calls, output, prefix, cursor and memory observations,
deriving wide copying from initial frames under explicit `memcpy_model`.
The canonical `Programs.Word.full_shift` dispatch through `compareVectorSize`
and `vectorComp vector2` selects the corresponding `full_left/right_shift1`
instance at depth log2(N)-log2(M). The source gate compares catalog bindings,
literal recursive combinators and concrete Coq specialization for both narrow
and wide families. These facts supplement kernel checking; they do not resolve
the remaining shared-domain or exhaustive per-entry review. See
`JET_FIDELITY_REVIEW.md` and `check-fullshift-specification.py`.

The 26 existing Bitcoin local-contract reviews remain scoped evidence in the
TimeLock/value, simple-getter and indexed/current review reports. Their exact
boundary diagnostic sources are now in `../../proof-work/review-witnesses/`.

## Corrections and inherited review, before additional coverage

Latest range receipt supersedes the historical repair journal below: the
reconciled candidate passes full acceptance with exit 0 (54683); all 149
guarded changes are integrated byte-for-byte. Actual-checkout acceptance is
passed with exit 0 as 24458, with matching final fingerprint. Coverage stays 349/533, and the
remaining endpoint/evaluator/domain/fidelity obligations remain open.

New isolated endpoint support now compiles and independently kernel-checks:
`writeBit`'s complete execution/output/prefix/cursor/framing contract works
when the accessed word's exclusive end is `max_unsigned + 1`. Six declarations
preserve the old contract's inclusion and a closed last-aligned-word arithmetic
witness. Accepted predicates and coverage are unchanged; no reachable Linux
allocation or all-caller generalization is claimed. The exact source/hash and
receipt are in `../../proof-work/range/WORD-ENDPOINT-SUPPORT.md`.

Negation review found the optimized `Word.adder` bit base differs structurally
from literal canonical `add`. The new shared canonical-add adapter is formally
proved equal under CoreFunSem for every width/input and independently
kernel-checked. That semantic bridge is now lifted through division's
approximation/correction loops, recursion, div_mod and modulo; the full
`fe_negate_literal_local_spec` compiles against this literal-add specification.
Independent whole-chain checking passes with exit 0 (32921), and the literal
port gate rejects 15 mutations. The algebra-independent parametricity module
also compiles (final closed), with kernel checking running as 90456.
Parametricity kernel checking now passes (90456). The expanded recursive gate
checks 48 typed declarations/16 Haskell regions and rejects 86 mutations.
A new all-width/integer formal state-conversion bridge compiles closed, with
kernel checking passing with exit 0 (1799). Remaining conversion/type/scribe/notation
source review now has a scoped gate passing 32 negative fixtures. Candidate
assembly, actual type/definition/assumption review and separate full acceptance
remain pending; the checkout's live audit inputs stay frozen. See
`../../proof-work/fe-negate/CANONICAL-REVIEW.md`.

1. Complete the same-block range correction. Its 19 unique unintegrated commits
   are preserved as a patch series in `../../proof-work/range/`. That archived
   candidate fails at `jet_full_multiply8_layout.v:122`. New isolated continuation
   patches repair full multiply, cell continuation, Bitcoin write effects,
   the symbolic frame invariant and its secp consumer; all five modules compile
   and pass independent whole-chain kernel checks, with unchanged statements.
   Six subsequent short-copy modules also compile and pass independent kernel
   checks: raw helpers now use byte-range separation, and the two initial-only
   cell contracts retain their statements and derive it from writable frames.
   Four further source-crossing modules compile and pass independent kernel
   checks with the cell contracts unchanged. The two-word left-copy helper
   and cell contract also compile and pass kernel checks, deriving separation
   for both destination words. Four analogous right-copy modules also compile
   and pass kernel checks, and the combined small-layout module compiles.
   Both small memcpy paths and the combined small-copy chain now compile and
   pass kernel checks with explicit `memcpy_model` retained. A whole candidate
   build exposed mixed-width sequencing, now repaired and kernel-checked with
   definitions/statements unchanged. Empty-buffer padding is now repaired and
   kernel-checked as well. Both broader build sessions have terminated; the
   write64/array sequencing chain is also repaired and kernel-checked.
   Parse-sequence conversion is repaired and kernel-checked; rotation control
   splitting is reduced without changing timeout bounds and freshly compiles.
   Its kernel check now passes with exit 0. The next fill-shift16 reduction
   timeout is repaired by bounded batching, freshly compiles and passes kernel
   checking. Fill-shift32 case generation is repaired and freshly compiles;
   independent kernel checking now passes. Fill-shift64 Qed is measured and
   bounded separately, and whole-module compilation passes. Independent width64
   kernel checking now passes. The next broader build stopped at Bitcoin array
   sequencing's old frame tuple. That consumer is repaired, freshly compiles,
   and passes independent whole-chain kernel checking. The following build
   stopped at wide-copy helper's obsolete block-distinctness claim. That helper
   now derives interval separation from capacity, freshly compiles and passes
   independent kernel checking with both execution theorem statements and
   existing assumption sets unchanged. The following build stopped at indexed
   scalar's final existential tactic. Goal inspection traces it to an earlier
   stale tuple introducing an index evar; correcting that tuple makes the whole
   module compile and pass independent kernel checking. The analogous
   input-value and indexed-pointer tuple repairs freshly compile; their
   independent combined kernel check passes. Value/hash output sequencing is
   repaired and its unchanged lemma compiles in a minimal isolated module;
   the original whole module remains under verification. The broader build
   stopped at tappath's analogous stale tuple; its repair freshly compiles
   and passes independent kernel checking. Empty-buffer writer layout also freshly
   compiles after deriving indexed/head separation, with kernel checking
   passing. Initialized SHA context-writer layout freshly compiles after the
   analogous capacity-derived separation repair and passes kernel checking.
   Present-buffer segment is the next repaired consumer: whole compilation
   passes and independent kernel checking passes. Mixed-buffer writer loop
   also freshly compiles and passes kernel checking. General SHA context
   reader/writer layouts freshly compile: the writer derives range separation,
   and the reader isolates byte-index arithmetic without changing deadlines.
   Their joint kernel check passes. Forward/reverse repair archive replay
   reproduces all 44 changed sources exactly; whole candidate compilation now
   passes with exit 0. All 44 repaired modules now pass independent whole-chain
   kernel checking, including the formerly lemma-only value/hash module.
   All 18 current accepted odd/zero sources compile unchanged against the range
   dependencies and retain their six inherited public assumptions. Complete
   independent kernel checking and reconciled full acceptance. All reconciled
   public chains and the complete assumption comparison now pass; the exact
   same-tree candidate build passes and independent full acceptance is running
   (session 54683, `../../proof-work/range/CONTINUATION.md`).
   All retain definitions and theorem
   statements. See
   `../../proof-work/range/CONTINUATION.md` for exact source hashes and receipts.
   Prior scoped kernel
   receipts and the 12 additional built/reviewed modules do not accept the full
   candidate. Repair consumers, review actual definitions/conclusions/hypotheses
   and snapshot differences, and finish independent acceptance.
2. Finish analogous address/representation and constructor-domain review, plus
   every pending registered chain to the literal canonical specification. The
   inherited matrix retains 284 registered rows needing more evidence. Do not
   infer fidelity from names, compilation, generated snapshots or admission
   scans. Keep domain restrictions and execution/output assumptions explicit.
3. Complete remaining raw Bitcoin getter and SHA/composed-hash boundary review
   identified in `JET_INHERITED_REVIEW.md`.

## Additional coverage and support, preserved but unaccepted

- Field addition: `../../proof-work/fe-add/` preserves six new original-C
  helper/representation modules (sixteen complete results). Fresh compilation and
  independent whole-chain kernel checking pass (43499, 15503, 95413, 62130,
  22804, 80818), with the
  existing axiom allowlist unchanged. The helper derives actual execution,
  output representation/framing and exact five output loads; the closed numeric
  bridges show non-wrapping sums, the existing wide-writer bound and the sum of
  input field representations. The owned-field composition derives actual
  helper execution, final field storage, both locals' Freeable permissions
  and outside-memory framing directly from initial owned fields.
  The complete two-reader/three-local public
  lifecycle and literal carry/add/normalize512 specification bridge remain
  open. These are unregistered support results, not increased jet coverage.

  Newer continuation supersedes that six-module milestone: ten modules/27
  results now compile. The writer representation/bounds bridge and literal
  field-add program also pass independent kernel checks (12352, 43323), for
  eight checked modules/22 results. The literal numeric interpretation and
  exact actual-limb-writer/literal-program comparison compile and pass independent
  kernel checks with exit 0 (89375, 6608), for ten checked modules/27 results.
  The two actual readers, combined
  environment, 512-bit frame invariant and three-local public lifecycle remain
  open. See `../../proof-work/fe-add/CONTINUATION.md` for the exact next boundary;
  no public registration or full acceptance is claimed.

  Combined reader environment and normalized-owned execution now also compile
  and pass independent kernel checks (15388, 85088), discharging bounds and
  numeric output assumptions for arbitrary raw Word256 pairs from the two
  stored normalized fields. Read-invariant rebasing and field preservation
  compile; rebasing's kernel check passes (78434), preservation's 84026 is live.
  This raises archived support to fourteen modules/39 compiled results, thirteen modules/36 with
  independent kernel receipts. The missing reader interface is the updated
  local source pointer/cursor from final representation; derive it before
  sequencing the second reader. `invA` capacity bounds outputs (256), not the
  combined input length (512); the continuation guide is corrected accordingly.

  Reader source-frame loads now pass independent kernel checking (34151), and
  the reader-call contract exposing them and actual two-reader execution both
  compile. Reader call kernel 65630 and strengthened two-reader kernel 17577
  pass; the latter exports both raw memory frames and supersedes 35352.
  Pair-input slicing (49538) derives both slices from the intended pair frame;
  actual add/write composition (35616) derives literal encoded output and both
  field locals' Freeable storage. There are nineteen archived modules/46 results,
  all independently kernel-checked. Four-call composition now also compiles,
  deriving literal output, all three locals' Freeable storage and composed
  outside-memory framing; independent kernel check 38991 passes (silent without
  context inventory). Actual public statement sequencing/return and three-local
  entry/free_list cleanup now compile; rest/entry kernel 59542 passes.
  Source-copy preparation, full public lifecycle and `fe_add_literal_local_spec`
  now also compile (96500, 50023, 7336): arbitrary Word256 pairs, six inherited
  execution assumptions, no libc model or assumed helper/output/cleanup facts.
  Total archive: 26 modules/63 compiled and kernel-checked results, plus two
  exact checker sources. Public check 91932 passes with `-o`, exact inherited
  axiom allowlist and no unsafe flags. The scoped field-add gate passes and
  rejects 52 mutations; reused recursive/literal/foundational gates also pass.
  Candidate assembly, reviewed snapshots, full acceptance and integration remain
  pending. See the archived `PUBLIC-CONTRACT-REVIEW.md` for precise review scope.
  Coverage remains unchanged.

- Field negation: `../../proof-work/fe-negate/` now preserves a complete original
  in-place C helper execution proof at magnitude one, with fresh compilation
  and independent whole-chain kernel checks passing. It derives actual calls,
  represented output and framing from initial owned storage, adding no axiom
  name or coverage. Five exact output loads and the non-wrapping numeric bridge
  now compile and pass independent kernel checking. Machine-limb normalization
  and the literal `fe_multiplyInt (-1)` / 512-bit modulo numeric bridges also
  compile and pass independent kernel checking with closed final assumptions.
  Three algebra-independent program proofs compile and pass independent kernel
  checking (51928). Two further modules compile: actual negation produces
  the field-memory representation with Freeable storage, and its actual
  normalization call produces the literal canonical negation's field value.
  Their joint kernel check passes (56432). Three shared wide-writer modules
  now compile: original expressions are interval-checked at 2^60, selected
  machine bytes denote the normalized field value, and the whole unchanged
  writer call derives output, finv, final represented storage and framing.
  Their independent joint kernel check passes (42447). Three further modules
  compile: input normalization does not change canonical negation, writer
  adapters retain exact output and Freeable storage, and combined actual
  negate/write calls derive canonical output, finv and composed framing.
  Their joint kernel check is running (62934). Initial reader facts and the
  complete public entry/source-copy/return/free remain open. Reuse this writer
  theorem; do not add a normalizer call before the public writer.
  Reader/writer wiring, literal correspondence gate and full
  public lifecycle/acceptance remain open. The
  separate untracked mathematical experiment is preserved unchanged.
- Field odd/zero: commit `cafb9b31` integrates 18 proof modules, two source
  checkers and registration/snapshot changes. The archived candidate remains
  under `../../proof-work/secp-field-predicates/` for provenance. There are 43
  new audited results, including two complete public jet contracts, not 43
  new jets. Fresh matching-toolchain kernel checks of both public modules pass;
  the literal-source gate rejects 34 meaningful mutations. A byte-for-byte
  comparison preserves all 3,534 prior assumption records and all prior printed
  types/definitions, with no new axiom names or kernel allowlist changes.
  Independent full acceptance passes with exit 0. The shared frame/domain review
  remains open; these results do not resolve it.
- Scalar/uint128: 22 complete helper sources and the historical literal-source
  checker are in `../../proof-work/scalar-u128/`. Eighteen match historical
  compiled/kernel receipts. Four require fresh verification, including a known
  prior compilation failure in `scalar_overflow_flags`. Subsequent shift64,
  scalar-reduce, numeric get-b32 and scalar-set-b32 helper work is preserved;
  the earlier executor diagnosis is not the current final stopping point.
  Canonical reduction/limb correspondence, read/write-scalar calls and complete
  public frame lifecycle chains remain open.
- SHA: the complete initialization/preservation source is preserved under
  `../../proof-work/sha-support/`; fresh compilation is reproduced on `cafb9b31`.
  Four additional compiled results derive frame/global separation from ordinary
  writable-frame predicates and preserve `sha_globals_ok` alongside the complete
  canonical block contract. Twelve shared Clight2 execution/memory results
  compile and pass independent kernel checking. Seven further compiled results
  derive a maximum-permission startup invariant and preserve it alongside the
  full canonical block contract, using the actual call derivation rather than a
  new permission-preservation premise. Allocation/store/storebytes setup steps
  also preserve that stronger state and derive fresh-block separation.
  They use existing CompCert external-call
  property axioms; actual assumption snapshots need review before integration.
  Startup facts come from the original global initializers. Remaining kernel/
  contract review and links at the other consuming public contracts remain open.
  The original startup module now also passes independent kernel checking.
  Four additional compiled results connect an operational fresh-private setup
  to the complete canonical block call and construct a real fresh frame;
  zero-length byte copies are allowed. The setup-to-block whole-chain kernel
  check passes with exit 0. Backing input/output buffer constructors, actual evaluator setup and
  general process-history admissibility still need review. Twelve concrete
  context-add/buffer/finalize ready contracts now compile through one shared
  lift, deriving globals from setup and preserving persistent state on both
  success and failure. They retain explicit `memcpy_model`; independent adapter
  whole-chain kernel checking now passes with exit 0 (15 allowlisted library
  axioms, no unsafe flags). A candidate-only boundary gate rejects 22
  mutations in catalog/adapters, full public contracts and operational setup.
  A further reviewed-port gate checks 26 typed Coq declarations and four
  Haskell implementation/type regions, rejecting 44 mutations. Underlying
  hash/word/assertion definitions, domain and snapshot review remain separate
  obligations. The scoped
  wiring review is `../../proof-work/sha-support/READY-CONTRACT-REVIEW.md`.
  This work does not add registered jet coverage.
  Five further results in `jet_sha_setup_frames` now compile: owned-block
  validity, fresh frame and frame-pair construction, represented input/output
  contracts preserved across setup, and a full canonical block call with both
  metadata records constructed from initial backing buffers. Independent
  kernel checking now passes with exit 0. Backing-buffer initialization and general
  evaluator/process-history admissibility are not discharged.
  Six additional results in `jet_sha_setup_words` compile and pass assumption
  printing. They construct storage by real allocations/private stores, build
  fresh output plus both metadata records, and derive a full canonical block
  call from a represented input. Independent whole-chain kernel checking passes
  with exit 0: 15 allowlisted library axioms and no unsafe kernel flags.
  Input initialization and general evaluator-history admissibility remain open;
  these construction witnesses do not narrow the general public contracts.
  Eight results in `jet_sha_setup_input` now compile and pass assumption
  printing. They derive canonical input cells from actual aligned stores,
  initialize all twelve words of every block-jet input, and conclude a full
  block call with input/output storage and both metadata records constructed.
  Independent whole-chain kernel checking passes with exit 0. It is a
  fresh-setup existence proof, not general evaluator-history admissibility or
  accepted additional coverage. Context/partial input initialization remains open.
  Fourteen results in `jet_sha_partial_running` compile, including twelve
  invariant-based adapters with the same concrete calls/specs/libc premises.
  They require and return persistent globals rather than fresh provenance,
  allowing global-state composition after verified calls. A boundary gate
  rejects 21 mutations. Whole-chain kernel checking passes alongside the constructed
  input consumer; per-result snapshot comparison, domain/dependency review, snapshots
  and integration acceptance remain open.

Each candidate manifest distinguishes historical evidence, complete source and
fresh acceptance. `python3 proof-work/manage.py` from the repository root checks
hashes and exact candidate-tree replay; it does not accept proofs.

## Removed transient material

`JET_PROGRESS.md` was a chronological continuation journal with superseded
pending/running checkpoints. Its durable status and source pointers are now
here and in the proof-work manifests; the full historical journal remains in
Git at `dcc600b7`. Its active references have been updated. The obsolete initial
prototype worktree is removed after putting its four untracked files in local
Trash for recovery. Generated artifacts, caches, raw logs and superseded open
goal diagnostics remain local.
