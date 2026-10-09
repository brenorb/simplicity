# Original point-infinity jet: direct-loop continuation

## Latest continuation (2026-10-09)

Fresh exact-source build **9386 passes with exit 0**. Standard contract
generation **48412 passes with exit 0**. Its actual extension adds 71 types
and 22 definitions without changing any baseline line. All types and 20
non-computed definitions match the prior deep prints modulo qualification/
whitespace; the two computational witnesses retain standard depth truncation
and are supplemented by deep prints and exact-source/kernel evidence.
Standard assumptions **70735** are live; poll them. After terminal success,
run `review-snapshots.py --baseline /tmp/jet-negate-accept.ftWsqQ/Coq
--candidate /tmp/jet-infinity-accept.xBQOUj/Coq
--preliminary /tmp/jet-gej-infinity.YrUC7w`, record its exact review, then
launch separate `check-jets.sh --accept` with no update flags. No registration
or checkout input has been changed. The checkout fingerprint still matches
its accepted `f87884d8...` receipt.

Isolated assembly is now `/tmp/jet-infinity-accept.xBQOUj`, based on the
accepted isolated 350-entry negation baseline, not the field-add candidate.
`ASSEMBLY.json` guards eight metadata files and all 22 exact proof/checker
sources. The isolated registry has 351 entries, but actual checkout remains
350: this is not accepted coverage. All 71 preliminary interfaces have been
reviewed, without claiming manual inspection of every generated trace node.
Scoped source/38 mutation tests and extended coverage negative tests pass
(38087 exit 0). Initial build 37054 passed with exit 0. Exact source hashes
then exposed one extra trailing newline from assembly; it was removed using
apply_patch after that build completed. Fresh exact-source build **9386**
is pending; log `build-exact.log`. Poll that run, do not restart it.
Next generate standard contracts and assumptions only in the isolated tree,
review additions versus the accepted baseline, then run full acceptance.
Do not integrate until that acceptance completes.

Separate field-add acceptance **54093 now passes with terminal exit 0**,
fingerprint `c4e91d0d6bbfb9d88fd63c40a802b5e052ecb8df2d54e51ec9b8a49e074b607d`.
Log `/tmp/jet-add-accept.qwqWy1/accept.log` includes all four AST matches.
Its guarded integration is still separate work, not an automatic overwrite
of the newer infinity assembly or current checkout inputs.

Preliminary actual-print checks now finish with exit 0: contracts 75319
(71 types, 22 definitions, deep print without truncation) and assumptions
18820 (all 71 records, 31 closed, each axiom set inherited-only). The final
public set retains six inherited execution assumptions. Exact inventories and
parsed assumption records are archived with hashes; `SNAPSHOT-REVIEW.md`
records the reviewed public/lifecycle interfaces and the still partial
helper-type review. This does not replace standard project snapshot generation
or extension comparison. Next finish that review and assemble an isolated
acceptance candidate. Do not integrate into or modify the live field-add audit.

Whole public-chain independent kernel **58930 passes with exit 0**, log
`/tmp/jet-gej-infinity.YrUC7w/gej-infinity-public-kernel.log`. Its 15 context
axioms are on the inherited allowlist and all three unsafe categories are empty.
All 71 archived results now have independent whole-chain kernel evidence.
The pure scoped `check-infinity-wiring.py` passes, and
`test-infinity-wiring.py` rejects 38 meaningful in-memory mutations. Both are
archived with source hashes. They check the literal recursive zero/point ports,
canonical record/catalog wiring, both application registrations, exact public
theorem, original C writer/jet bodies and public allocation/copy/free call
wiring. This supplements formal proofs and AST regeneration; it is not an
exhaustive transitive fidelity or evaluator-domain certificate.

Reproduce using `python3 -B` on the materialized checker/test, passing
`--repo /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity`
and `--candidates /tmp/jet-gej-infinity.YrUC7w`.
Remaining promotion work: exact type/definition/assumption snapshot review,
isolated complete acceptance, guarded integration and actual-checkout acceptance.
The candidate remains unregistered; current coverage is not increased.

The complete public contract now **compiles freshly with exit 0** (39500):
`C.jet_secp_gej_infinity_local.gej_infinity_literal_local_spec` has type
`secp_jet_local_spec f_simplicity_gej_infinity Ty.Unit
  (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8))
  (@literal_gej_infinity Alg.CoreFunSem)`.
It derives the real 16/128-byte allocations, by-value source frame copy,
initializer, three-coordinate writer, true return and actual freeing, followed
by the common output/prefix/cursor/outside-memory conclusions. The final
assumption print retains six inherited execution assumptions, no new names
and no `memcpy_model` premise. Initial helper-call/output/freeing facts are not
public premises. The Unit input is handled by destructing its sole value,
not by narrowing any nontrivial input domain.

The four new archived modules add 10 results (71 freshly compiled in total):
`jet_secp_gej_public_lifecycle` (10393),
`jet_secp_gej_public_prepare` (fresh compiler terminal exit 0),
`jet_secp_gej_public_call` (62103), and
`jet_secp_gej_infinity_local` (39500).
Owned-remainder kernel 86825 passes with exit 0, inherited allowed context,
all unsafe categories empty. Whole-public-chain independent kernel **58930**
is pending, log `gej-infinity-public-kernel.log` in the scratch root; all its
inputs are frozen. This is still **unregistered candidate coverage**.

Next: poll 58930 rather than restart; inspect its inherited context/unsafe
summary; cross-check the literal Haskell program, CoreJets binding/type and
exact original public AST/lifecycle, with meaningful negative source-gate
tests. Review actual new type/definition/assumption snapshots. Assemble an
isolated full acceptance candidate, then guarded integration and separate
checkout acceptance. Do not count this jet merely from compilation.

Earlier entries below record superseded development boundaries, not the
current remaining proof obligations.

`exec_gej_public_rest_owned` now compiles freshly (23493 exit 0), with the
same six inherited execution assumptions. Its archived source
`jet_secp_gej_public_rest.v.source` derives both actual helper calls from
initial point/frame Freeable ranges and the initial `finv`; it concludes the
actual public remainder and true return, literal encoded output, final frame
invariant, both Freeable ranges and outside-local/non-frame load preservation.
This discharges the prior from-calls adapter's premises, not by adding them
to the public contract. Public-body kernel 49541 passes with exit 0, inherited
allowed context and all unsafe categories empty. Owned-remainder whole-chain
kernel 86825 is pending; log `gej-public-rest-kernel.log` in the scratch root.
Compiled support count is 61, with the first 60 independently kernel-checked.
Next connect real allocation and source copy, then actual `Mem.free_list`,
to the complete `secp_jet_local_spec`; do not register coverage before that.

After the range cleanup, the signed range commit `805cb19e` is merged locally
into `feat/jet-equivalence`. Audited Coq inputs retain fingerprint `f87884d8...`:
actual checkout acceptance 57052 finished with exit 0. The pre-merge stash
`382ca5dc7a0e828702a93d15ab5d2057ade24786` retains both working and staged
versions, plus untracked files. The merged branch and clean worktree were pruned.

`jet_secp_gej_public_body.v.source` adds five freshly compiled results
(83088 exit 0), bringing compiled support to 60. It proves the exact public
body, actual symbol linkage, initializer/writer call adapters and boolean return
composition. Whole-chain independent kernel 49541 is pending, log
`gej-public-body-kernel.log` in the scratch root. Its from-calls theorem is an
intermediate adapter, not final correctness: derive both calls from initial
storage, preserve frame/source-local ownership, perform the real source copy,
and free both public locals. No new coverage is registered.

The earlier symbol lookup timed out because `vm_compute` reduced an existential
goal over the whole generated environment. Providing `secp_symbol_block` first
and using conversion (`reflexivity`) proves linkage quickly without hardcoded
block numbers. Do not raise reduction limits for that former experiment.

Four additional archived modules contribute 14 freshly compiled results:
`jet_secp_literal_infinity.v.source` (69999),
`jet_secp_point_write_preservation.v.source` (77215),
`jet_secp_point_three_writes.v.source` (77443), and
`jet_secp_write_gej_infinity.v.source` (31463), all exit 0.
Independent whole-writer kernel run **34554 passes with exit 0**, log
`/tmp/jet-gej-infinity.YrUC7w/write-gej-infinity-kernel.log`.
All 15 context axioms belong to the inherited allowlist; all three unsafe
categories are empty. The archive has **54 independently kernel-checked
support results**, not a newly registered public jet.

The literal constant port retains `(fe_zero &&& fe_zero) &&& fe_zero`.
Other-coordinate loads are preserved across each actual field write using
the precise 40-byte field footprint within the real 128-byte point allocation.
`eval_write_gej_infinity_literal` derives the actual complete original
`f_write_gej` call, literal encoded output, cursor/prefix invariant, point
Freeable preservation and outside-point framing from initial storage facts.
No helper execution or output premise is assumed in that final writer theorem.

The public wrapper remains open: connect its real 16/128-byte allocations,
by-value source copy, initializer, writer, boolean return, and freeing both
locals into the general public jet contract. A fresh scratch entry lemma
`gej_infinity_public_entry` compiles (75321 exit 0, closed under the global
context); its independent kernel run **54535 passes with exit 0**, inherited
allowed context and all three unsafe categories empty. It is now archived
byte-for-byte, bringing the checked support count to **55**, not jet coverage.
Do not confuse the internal writer or entry with public completion.

Older sections below retain the development history and earlier boundaries.

The target is public `simplicity_gej_infinity`, not an internal constant
mistaken for a public jet. Canonical CoreJets maps GejInfinity to the record
in LibSecp256k1.hs:502: `(fe_zero &&& fe_zero) &&& fe_zero`, with `fe_zero`
defined as `zero256`. Original C sets a 128-byte point local to infinity and
calls `write_gej`; the generated public function also allocates/copies its
16-byte by-value source local. No production code or canonical term is edited.

## Verified boundary

Scratch `/tmp/jet-gej-infinity.YrUC7w`, narrow overlay `-R` to namespace C.
`jet_secp_fe_clear_loop.v` compiles freshly with exit 0 (84028), using
Coq 8.17.1, 65520 KiB stack and `build-jets.sh --coqc` in the checked baseline
`/tmp/jet-negate-accept.ftWsqQ/Coq`. It contains 13 completed results.
Independent whole dependency kernel run **97583 passes with exit 0**, with
`-silent -o`, log `clear-loop-kernel.log`. Its 12 context axioms are a subset
of the inherited 15-name allowlist; all three unsafe categories are empty.
The final support theorem prints only six inherited execution assumptions.

The loop source proves the exact generated `fe_clear` body, actual guard/exit,
increment, composite member/offset layout, array address and C pointer
arithmetic, actual store statement, finite loop, entry and complete original
helper call **from a concrete five-store witness**. The new memory source now
derives that witness by induction from initial Writable storage, with all five
zero loads, exact permission preservation and outside-range loads. Its
`eval_fe_clear_owned` composes actual execution and the zero field `fe_at`
directly from initial storage, without assumed stores or executions. It
compiles freshly with exit 0 (21001), adding two results, for **15 total**.
Its independent whole-chain kernel check **31232 passes with exit 0**, with
`-silent -o`, log `clear-memory-kernel.log`. Its 12 context axioms are a subset
of the inherited 15-name allowlist; all three unsafe categories are empty. This is internal support,
not a public jet equivalence or coverage.
No assumed execution/output fact is introduced as a public precondition.
The archive matches the checked source byte-for-byte and is included in the
archive materializer/integrity checker.

## Why the first executor attempt failed

The original executor returns `None` for `fe_clear` and consequently for the
point initializer: arithmetic/comparison expressions over closed constants
remain symbolic. After increment, pointer indexing no longer sees `XIc`;
the symbolic loop also explores the alternate branch. The failed initial
experiment `jet_secp_gej_infinity_init.v` remains outside the repo and build;
its proposed run equality did not compile and must not be reused as a proof.

Use the direct loop pattern from `jet_write32s_exec.v`, as implemented by this
new source. Do not raise the executor fuel repeatedly, assume the helper call,
replace the C loop, or silently rewrite the generated function. A generated
composite includes proof-heavy metadata: computing its complete value timed
out. Computing only `option_map co_members` closes the small layout fact;
destruct the original lookup and derive its field offset from that member list.
Pointer addition uses `Ptrofs.mul` before `Ptrofs.add`, not a convertible
unbounded product. The bounds prove the actual signed index and pointer casts.

## Next substantive work

The complete **original initializer** now compiles, not just the flag/loop.
`jet_secp_gej_infinity_body.v.source` adds four results for the unchanged
body, the actual helper-call statement, entry and three-call composition
(20715 exit 0). Symbol linkage comes from `secp_pure_ok`, not block numbers.
`jet_secp_gej_infinity_owned.v.source` adds two results (15999 exit 0):
zero-field preservation and `eval_gej_infinity_initializer_owned`. The latter
derives the actual flag store and all three original helper calls from initial
Writable point storage, concluding the actual full initializer call, zero
fields at offsets 0/40/80, infinity flag, exact global permissions, valid
blocks and outside-point loads. No store, call, output or cleanup premise is
assumed. Its six execution assumptions are inherited. Independent whole-chain
kernel session 67307 now passes with exit 0, log `infinity-owned-kernel.log`
in the scratch root; its context is inherited and all three unsafe categories
are empty. All 28 compiled support results now have independent terminal
kernel receipts. This proves the internal initializer, not the public jet.

The point-slice **original field writer** now has 12 freshly compiled results
in three new archived modules. `jet_secp_point_write_run.v.source` (92355
exit 0) runs the unchanged `f_write_fe` with field pointers at 0/40/80 in one
base-zero, 128-byte Freeable region. Only the selected field's cells need
representation; no fictitious separate field allocation is introduced.
Its exact selected output-event log matches the existing ordinary writer,
and its final storage metadata retains ownership of all 128 bytes.
`jet_secp_point_write_exec.v.source` (64437 exit 0) derives the real writer
call, encoded field output, full `finv`, outside-cell framing and full-point
Freeable preservation. `jet_secp_point_write_initial.v.source` (85592 exit 0)
derives the needed initial representation from actual field storage and the
point allocation's ownership, then the full owned-field writer contract.
Its final statement has no execution/output/cleanup assumption.

Fresh independent whole-chain kernel session 99341 passes with exit 0, log
`point-write-fresh-kernel.log`, inherited context and all three unsafe categories
empty. These sources are archived byte-for-byte. The
earlier premature run 67469 targeted an older compiled initial-representation
artifact while the extended source failed from a missing import. That exact
owned experiment was intentionally terminated (exit 143); it is not a receipt
for the current source. Fresh compilation 85592 completed both declarations
before the replacement kernel run. No other audit was stopped or changed.
All 40 compiled support results now have independent terminal kernel receipts.
The public point-infinity jet still requires the actual three-coordinate writer
composition, literal constant-program bridge and public entry/cleanup chain.

Next substantive boundary is the **real three-call point writer**, then the public
16/128-byte-local lifecycle and literal constant program. Existing
`eval_write_fe_from_canonical_field` supports arbitrary field offsets but does
not expose Freeable preservation inside the written field. The local wide
writer preserves that permission through `rfree`, but its representation
explicitly requires region base zero (`rep_free_region`). Do not instantiate
that theorem at offsets 40/80 or assert whole-point cleanup follows from
Writable storage. Either prove the required permission preservation for the
ordinary original writer, or derive a point-wide 128-byte owned representation
through the actual original writer execution (now implemented above). Retain the existing three real
`write_fe` calls and full prefix/cursor/memory observations.

Point layout and the original flag statement now have six freshly compiled,
independently kernel-checked results (84656/61438, exit 0), archived as
`jet_secp_gej_infinity_layout.v.source`. They prove the exact generated field
offsets, field/address expression semantics and flag assignment. The separate
`jet_secp_gej_infinity_flag_memory.v.source` derives that actual statement
from initial Writable point storage, with the flag load, exact permission
preservation, valid blocks and outside-flag loads. It compiles with exit 0
(20256); independent whole-chain kernel session 70092 now passes with exit 0,
12 allowlisted context axioms and all three unsafe categories empty. All 22
compiled support results have terminal independent kernel receipts. This is
still support work: initializer composition and the public jet remain open.

An offset-equality option injection initially timed out by unfolding the
large composite environment. After inspecting the goal, the layout proof was
decomposed through a separately computed member list, as for `fe_clear`.
Only the small resulting concrete offset expressions are computed. Do not
return to inversion/injection of the proof-heavy environment expression.

1. Store derivation, the original helper contract and their independent kernel
   checks are complete. Exact permission preservation transports
   any initial Freeable permissions, including the enclosing point region.
2. The original initializer's flag store and its three original `fe_clear`
   calls at offsets 0, 40 and 80 are now composed. Exact global permission
   preservation transports the enclosing 128-byte Freeable region.
3. Compose the new real field-slice writer for each zero coordinate, deriving the actual
   `write_gej` call and 768-bit literal encoded output, prefix, cursor and
   outside-memory observations. Derive each intermediate invariant/storage
   fact rather than add it as a public premise.
4. Derive actual public entry, source-copy, initializer/write/return/free for
   the 16/128-byte locals, then the complete literal `secp_jet_local_spec`.
   Source correspondence gates, snapshots and separate full acceptance follow.

The last completed checkout acceptance covers 349/533. Negation candidate
acceptance 57174 passed and is guarded-integrated; registry 350/533 remains
provisional while actual checkout acceptance 57052 runs. Field-add build
24847 and standard contract generation 57349 passed; its exact 63-type/20-def
contract diff is reviewed. Assumption generation 71393 passed, preserving all
3670 prior records and adding exactly the reviewed 63 records. Separate frozen
full candidate acceptance 54093 is now live.
Their proof inputs remain untouched. No commit or
push is claimed while the signing agent remains unavailable.
