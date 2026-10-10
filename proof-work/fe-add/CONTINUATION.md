# Field-add continuation: exact next boundary

## Current authoritative boundary

Latest update: serial checkout acceptance **86431 exited 0**. Fresh compilation,
652-module kernel check, 3733-result assumption audit (1948 closed), reviewed
public contracts/definitions, negative gate tests and all four AST regeneration
checks passed. Input fingerprint stayed exactly
`16594c779a885f405041d02315d3cbaec414f439dc78c3d219dde3a8b425f631`.
The receipt and log hash are in `INTEGRATED-ACCEPTANCE.json`. Its input freeze
is released; do not restart the finished audit. Historical running/failure
paragraphs below are superseded. Unregistered point candidates still require
their own standard snapshot review and isolated acceptance; this does not
complete the every-jet goal.

Unchanged-input serial full acceptance retry **86431 is live**, log
`/tmp/jet-add-integrated-accept-serial-2026-10-09.log`. It uses `JOBS=1`, all
original tactic deadlines and all acceptance gates; no update/no-build flags.
Input fingerprint remains
`16594c779a885f405041d02315d3cbaec414f439dc78c3d219dde3a8b425f631`.
Heavy infinity assumption printing has completed (70735 exit 0), and its
read-only standard snapshot review passes (56302 exit 0). Poll 86431,
preserve the prior failed log and keep actual audited inputs frozen.
Full checkout acceptance has not yet passed. Older milestones follow.

Checkout run **96671 is terminal exit 2**, not live: unchanged
`jet_copyBits_two_words_left.v:139` and `jet_shift16_with_spec.v:26`
hit their existing tactic timeouts while the separate full assumption
printer was consuming CPU. Both files remain byte-identical to the accepted
negation baseline, and the integrated input fingerprint is unchanged.
The log is retained. Diagnose/retry serially after heavy printing ends;
do not raise timeouts blindly, skip proofs or claim checkout acceptance.
Isolated field-add acceptance 54093 remains a valid separate receipt.
The independent point-predicate accessor is developing outside audited trees.

Latest integration boundary (2026-10-09): isolated full acceptance **54093
passes with terminal exit 0**, including fresh build, kernel, reviewed
snapshots, negative tests, four ASTs and unchanged input fingerprint
`c4e91d0d6bbfb9d88fd63c40a802b5e052ecb8df2d54e51ec9b8a49e074b607d`.
All ten infrastructure guards matched the checkout baseline; the 26 new
proof paths were absent and their candidate/archive hashes matched; both
existing snapshots exactly matched the accepted negation baseline.
After applying the reviewed extension, all **38 integrated files** exactly
match that accepted field-add candidate. No production C/Haskell change.

Signed local source commit **62350724** contains only 26 new proof modules
and two new scoped source checkers, not unrelated staged metadata/work.
The working-tree registry is now 351/533 (247 direct-style, 104 conditional);
the separate full checkout acceptance **96671 is live**, log
`/tmp/jet-add-integrated-accept-2026-10-09.log`, input SHA-256
`16594c779a885f405041d02315d3cbaec414f439dc78c3d219dde3a8b425f631`.
Poll this handle; do not restart it or edit any audited checkout inputs.
The point-infinity audit is separate and unregistered. Its eventual
integration must reconcile this newer field-add extension, not overwrite
shared inventories, registry, tests or snapshots from its older baseline.
Remaining paragraphs preserve superseded development milestones.

The complete `fe_add_literal_local_spec` candidate compiles (7336): the full
existing `secp_jet_local_spec` for original `f_simplicity_fe_add`, arbitrary
Word256 pairs and `literal_fe_add`. Preparation (96500) derives actual source
copy and invariants after three allocations; lifecycle (50023) derives actual
entry/body/return/free. Final assumptions are the six inherited execution
assumptions, with no `memcpy_model`, assumed helper calls/output/cleanup or
operand bound. This is a compiled formal candidate, not accepted coverage.

Archive: **26 modules / 63 completed results**. The original 23 modules / 58
results have independent kernel receipts, including rest/entry 59542 (exit 0).
Public whole-chain check **91932 passes with exit 0**, with `-silent -o`, log
`/tmp/jet-fe-add-next.3vEywc/public-kernel.log`. The printed axiom names match
exactly `Coq/C/jet_coqchk_axioms.expected` (15 names); all three unsafe categories
are empty. All 26 modules/63 results now have whole-chain kernel evidence.
Two exact additional checker sources are archived, bringing source rows to 28.
The field-add wiring gate passes and rejects 52 in-memory mutations. Reused
recursive/literal/foundational gates pass and reject 86+15+32 mutations.
`PUBLIC-CONTRACT-REVIEW.md` records the precise source/lifecycle/domain scope.

Snapshot preparation now enumerates all **63 named results and 20 transparent
definitions** in `public-results.txt.source` and
`contract-definitions.txt.source` (30 archive rows total, still 26 proof modules).
Isolated actual type/body/assumption printing **passes with exit 0 as 84352**, log
`/tmp/jet-fe-add-next.3vEywc/snapshot-review.log`, driver
`field_add_snapshot_review.v` in the same scratch root. This does not mutate
accepted/candidate snapshots. All records are present: 31 closed, 2 funext-only,
12 inherited logical, 18 inherited logical/execution; no new axiom name occurs.
Inspection found default printer abbreviations in deep terms. A deeper run
**55290 passes with exit 0** with `Printing Depth 10000`,
`snapshot-review-depth.log` (2211 lines): no `(...)` remains, all inventories
match and all assumption sets are unchanged. Full newly exposed definitions
were reviewed. Provisional actual per-result assumptions are archived as
`assumptions-provisional.expected.source` (31 archive rows, 26 proof modules).
`SNAPSHOT-REVIEW.md` records the precise scope. This is preliminary review, not
approval of an old-record diff or a full acceptance receipt. The original
hyphenated driver filename failed before compilation; the valid underscore
name is used by this live run.

Isolated assembly has now completed at `/tmp/jet-add-accept.qwqWy1`, without
waiting for or modifying negation's separate live acceptance. Its dependencies
remain checked-but-unaccepted; assembly alone does not promote them. All 893
unchanged inherited audited inputs are byte-identical, the 26 proof hashes and
ten infrastructure hashes match, and actual coverage/negative/source tests pass
(20653, exit 0). Whole fresh build **24847 passes with exit 0**, `build.log`.
Standard assumption/contract snapshot generation is now live as **71393** and
**57349**, with respective `assumptions-update.log` and `contracts-update.log`.
Poll these exact handles; review remains pending. `ACCEPTANCE-CANDIDATE.md`
records the reproducible boundary.

Next work:

Exact acceptance infrastructure is preserved in
`acceptance-infrastructure.patch` and guarded by `INTEGRATION-PREPARED.json`.
It adds 26 modules to both project inventories, 63 named results and 20
definitions, exactly one final coverage row, the secp metadata adapter with
four negative fixtures, and both field-add source gates to acceptance. The
two `.py` checkers are fingerprinted automatically by the existing audit.
`git apply --check` passes against the frozen negation candidate; all ten
base/output hashes match. An in-memory overlay passes inventory checking at
provisional 351/533 and rejects all four new metadata mutations. The scoped
source gate still rejects all 52 mutations. Preparation did not edit the
negation candidate. Subsequent isolated assembly is recorded above; no new
snapshots were generated or approved, and accepted coverage stays 349/533.
The exact guarded patch is now applied only to the isolated candidate above.
Revalidate the base hashes after negation acceptance/integration before any
different application or checkout integration.
The patch does not supply either acceptance snapshot: generate and review those
separately in the isolated assembled candidate, then accept without update flags.

1. Poll snapshot sessions 71393 and 57349 to terminal status, then review
   actual type/definition/assumption diffs, preserving all old records. Deeper
   preliminary field-add printing/review is complete; retain its receipts.
2. Separate full acceptance without update flags, guarded integration, then
   actual-checkout acceptance before coverage registration.

Coverage remains 349/533. Range actual-checkout acceptance passed and its
fingerprint still matches. The signing agent was rechecked with proper access,
but refused signing; no unsigned commit, settings change or push was made.

## Historical progression (superseded by the public candidate above)

Nineteen archived modules compile, with 46 completed results. All original
fourteen modules/39 results have completed independent whole-chain kernel
checks; preservation passes with exit 0 (84026), exact inherited allowlist and
no unsafe flags. Source-frame loads also pass (34151, exact inherited allowlist,
no unsafe flags). Reader call check **65630** passes. The strengthened two-reader
contract exporting both raw memory frames passes **17577**, superseding the
old version checked as **35352**. Pair-input slicing passes **49538** and the
actual add-helper-plus-writer composition passes **35616**. All nineteen modules
are independently kernel-checked with the exact inherited allowlist and no
unsafe flags; archive hashes and scratch bytes match exactly.
Logs: `read-source-kernel.log`, `read-cursor-call-kernel.log`,
`two-reads-framed-kernel.log`, `pair-input-kernel.log`, `add-write-kernel.log`
under `/tmp/jet-fe-add-next.3vEywc`. These are terminal receipts.
Logs are `/tmp/jet-fe-add-next.3vEywc/literal-numeric-kernel.log` and
`literal-writer-kernel.log`. Preserve these terminal receipts.
The compiled theorem `add_writer_literal_output` has functional extensionality
alone, inherited from the division bridge. It is an intermediate output bridge,
not full public execution or accepted coverage.

Coq dependency roots: original six modules compiled against independently
accepted range `/tmp/jet-range-consumer.RbIhbg/Coq`; the four new modules compile
against `/tmp/jet-negate-accept.ftWsqQ/Coq`. Narrow scratch overlay:
`-R /tmp/jet-fe-add-next.3vEywc C`. Coq 8.17.1, stack 65520 KiB, commands through
`build-jets.sh --coqc/--coqchk`. Keep all scratch outside accepted inventories.

## Next substantive work

Fresh continuation: `jet_secp_add_calls` compiles (6734), adding two results:
closed `no_field_add_foot` and `eval_field_add_four_calls` with exactly six
inherited execution assumptions. The latter derives all four original calls,
literal encoded output, all three Freeable locals and composed outside-memory
framing directly from the canonical pair input and initial owned storage.
Independent whole-chain kernel check **38991** passes with exit 0. Its log is
silent because this invocation omitted `-o`; the library-wide context inventory
was not printed, unlike earlier receipts. Final theorem assumption printing
still confirms the six inherited execution assumptions.
Three further modules compile: `jet_secp_add_body` (72780, six results),
`jet_secp_add_rest` (27239, one result) and `jet_secp_add_entry` (52049, three
results). The original statement suffix now derives calls and return directly
from initial frames; entry derives the actual three allocations, and cleanup
derives the exact environment's free_list from their Freeable permissions.
Current archive: twenty-three modules/58 compiled results; twenty modules/48
have completed independent kernel checks. Combined rest/entry whole-chain kernel
check **59542** is live in `rest-entry-kernel.log`; it is also silent without
`-o`. Do not restart on yield. Obtain the expanded dependency context with `-o`
in the next justified combined verification, and compare the inherited allowlist.
The next substantive step is three-local source-copy preparation and composing
entry/body/return/free into the actual public call and full contract. No public
coverage is added.

1. Combined normalized limb environment, values and 52-bit bounds are now
   complete in `jet_secp_add_reader_environment`. `normalized_add_reader_facts`
   discharges them for arbitrary raw Word256 inputs; actual helper execution
   and literal output equality follow in `eval_field_add_from_normalized_fields`
   from the two stored normalized fields. These are intermediate storage
   preconditions, not proposed public input restrictions.
2. Source pointer/cursor cells and actual loads now compile, derived from final
   `rep`; `eval_read_fe_canonical_with_source` exposes them from the actual call.
   `eval_add_two_readers` now derives both calls, both normalized stored fields,
   source cursor `rc+512`, all three locals' Freeable permissions and the final
   read-only invariant. `field_pair_input_slices` now derives both reader slices
   from the literal pair encoding, and the strengthened reader contract exports
   `HFrameA` and `HFrameB`. Do not add reader slices as public premises. Preserve
   the first local's
   loads and Freeable storage. Inspect original `f_simplicity_fe_add` (at
   `Coq/C/jets_secp.v:201688`): `_src` is 16 bytes, `_a` and `_b` are 40 bytes.
   The body copies its by-value source, calls `read_fe` twice on that same
   advancing source, calls the original in-place add helper, then `write_fe`,
   then returns true. Negation's one-field allocation/entry cannot be relabeled
   to prove this three-local case.
3. `eval_add_write_calls` now composes the actual helper and original writer,
   deriving literal encoded output, both fields' Freeable permissions and raw
   add/write memory frames from stored reader results and read-only `finv`.
   `eval_field_add_four_calls` now compiles that composition, preserving
   source-copy Freeable storage through add/write and outside-three-locals
   framing. Its independent kernel receipt remains pending as noted above.
   Compose source cursor advances for 512 input bits,
   but retain **256 output capacity**: `invA`'s `capA` bounds writes, not reads.
   Rebase the read-only invariant to the next reader environment separately
   from proving actual source-frame fields/cursor. Preserve both field locals and the
   source-copy local's Freeable permissions for actual public cleanup.
4. Complete entry/source copy/body/return/free and public encoded output,
   prefix/cursor/load framing. Do not export intermediate assumed executions,
   outputs or reader facts as public preconditions.
5. Freeze literal source correspondence: Haskell `LibSecp256k1.hs:480`, `Arith`
   add and one, conditional carry expansion and `fe_normalize512`. Reuse the
   negation add/division/foundations gates. Add mutations that alter either
   carry branch, one/zero, input domain or actual C function/cleanup chain.
   Then review snapshots, run full acceptance and integrate with exact guards.

The canonical one program is `true >>> left_pad_low word1 word256`, not an
unjustified integer constant. The scalar-add literal port has the same carry
expansion (`LibSecp256k1.hs:580`), but its modulus and C representation differ;
reuse only after field addition has a complete verified public contract.

Separate audit **57174** (negation candidate) remains live with frozen inputs.
Actual checkout range audit **24458** passes with exit 0 and a matching current
fingerprint; its freeze is released. No coverage is added
by these support modules; accepted registry remains 349/533.
