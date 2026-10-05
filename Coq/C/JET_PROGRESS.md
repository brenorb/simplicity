# Original-C equivalence continuation

The previously published acceptance receipt is `JET_ACCEPTANCE.md` at
`61de9183` (319 registered contracts). This continuation has now passed its own full
reviewed-snapshot acceptance (exit 0); integration/publication follows the
atomic commits recorded at the end. Historical running checkpoints below are
superseded by this result.

## Completed source review and compiled bridge

Twelve `full_left/right_shift_64_{1,2,4,8,16,32}` contracts retain the actual
`f_simplicity_*` calls, output, prefix, cursor and outside-footprint observations.
They derive the wide copy from initial frames, under explicit `memcpy_model`.
The canonical catalog calls `Programs.Word.full_shift`, not the narrower helper
by name: its `compareVectorSize wb wa` dispatch and `vectorComp vector2` select
exactly the `full_left/right_shift1` instance with depth log2(N)-log2(M).
`Ty/Word.hs:125–148`, `Programs/Word.hs:163–190`, and the 36 catalog bindings
were inspected. The new specification gate compares catalog binding, the literal
recursive combinators and the concrete Coq specialization. It supplements, and
does not replace, kernel checking. Regression fixtures reject catalog, depth and
recursive-dispatch drift. Both narrow and wide families are checked.

Two new raw annex getter contracts compile in
`/tmp/jet-annex-raw-compile-final.log` (exit 0). The indexed getter preserves the
outer missing-index sum, inner absent-annex sum and hash of the actual annex
bytes. The current getter interprets the literal CurrentIndex/assert composition:
missing current input fails; missing annex succeeds with the inner sum. Existing
Clight calls and output/memory guarantees are transported through the checked
raw projection, rather than assumed. The earlier failed compilation was an
uninstantiated semantic-function evar; the exact existing primitive semantics is
now supplied explicitly. Its inspected goal is in `/tmp/jet-annex-goal.log`.

Fifteen Bitcoin registrations are added: the existing raw tappath contract, two
new raw annex contracts, total input/output/fee, and nine TimeLock contracts.
Their literal forWhile/add/subtract, finality loop, parseLock/parseSequence,
version>=2 and assertion/comparison definitions were compared with the pinned
Haskell Transaction/TimeLock programs. Amount sums are modulo 2^64 over the full
Word64 domain. Cached finality is exactly forall(sequence==0xffffffff), matching
`C/bitcoin/env.c:100–116`; totals match its uint64 accumulation. These are initial
environment representation facts, not execution/output assumptions.

The four assertions retain `application_jet_partial_spec`: actual C execution
and the exact option-dependent boolean return on every input, successful
output/cursor/prefix, and memory framing in both cases. Failure has no specified
output value, as in the existing assertion contract; the definition is frozen.
Coverage accepts only that entire proposition for the precise public function,
`bitcoin_ge` and `Bitcoin.env`. Negative fixtures reject wrong functions, linked
programs, cache-only environments and added impossible premises.

## Pending acceptance scope

Static source-target, coverage, specification-binding and negative checks pass.
The conservative candidate registry is 346/533: 242 without an extra libc
premise, 104 conditional on libc, and 187 without a registered final equivalence.
Of the 27 additions, twelve are conditional core shifts and fifteen are Bitcoin.
There are three new public results and five newly frozen definitions. Production
C, canonical Haskell, generation inputs and compiler flags remain unchanged.

The full candidate audit must complete, its type/definition/axiom differences
must be reviewed, and `check-jets.sh --accept` must pass without update flags
before committing, integrating and publishing this continuation. No integer
normalization, byte/limb model, symbolic tree or SHA global-state premise is
promoted by this registration change. Remaining SHA startup/preservation, raw
composed hashes, secp canonical bridges and Elements obligations remain open.

## Running candidate audit

The frozen candidate audit is running in the existing review worktree:
`/Users/brenorb/.codex/worktrees/claude-consolidation/simplicity`.
Its log is `/tmp/jet-next-canonical-candidate.log`; unified execution session
`53393` must be resumed rather than launching a second compiler. Observed during
this continuation: all static gates passed, build was up to date, and the native
`coqchk` process was active. No final audit exit status is available yet.
The command uses the pinned OPAM/CompCert/VST toolchain, `JOBS=2`, and
`bash Coq/check-jets.sh --update-expected --ast`. Once it finishes, inspect its
actual status and review all snapshot differences before the separate
`--accept` run. Do not edit audited inputs while either run is active.

The published fork branch was rechecked and remains
`61de9183801726770058bd3df669f3a2b962440a`. This continuation has not been
committed, integrated, or pushed. The upstream repository and main/master
branches have not been changed.

## Isolated SHA startup/preservation support

While the candidate inputs are frozen, the next SHA obligation was developed
outside the repository in `/tmp/jet_sha_initial_globals.v`. The complete file
compiles with exit 0 under the pinned toolchain; its final log is
`/tmp/jet-sha-global-preservation-compile-final.log`. It contains 16 checked
lemmas/theorems and one state definition. It has not been added to the project,
registered as coverage, committed or published.

The initial dispatch load follows from the actual `Init_addrof` initializer
and `Genv.init_mem_characterization`. The counter load and absence of writable
permission follow from the real readonly `Init_int64` initializer. The mutable
dispatch block has exactly the initialized eight-byte permission range. Those
facts form a state invariant derived from actual initialization, rather than
an assumed execution/output result.

Preservation is proved for allocation, freeing other blocks, scalar stores
outside the dispatch block, long-cell and cursor stores, and positive-length
`Mem.storebytes` outside the dispatch block. Fresh allocation proves that locals
differ from both globals. Cursor writes derive dispatch separation from their
base/range; long-cell writes derive it from the loaded Vlong versus Vptr and the
eight-byte permission range. Successful stores themselves rule out writes to
the readonly counter. The byte-copy lemma preserves the libc trust boundary;
it proves the `storebytes` effect, not the linked libc implementation.

An initial conversion timeout was isolated to eager reduction of the concrete
program while checking the AST/global-environment correspondence; keeping the
unchanged program opaque and reducing only the environment projections closes
that conversion within the original timeout. A later failed allocation proof
had two shelved permission-kind variables; inspection with `Show Existentials`
identified them, and explicit `Cur Readable` witnesses removed them. The final
complete compiler run, not those failed prefixes, is the evidence recorded here.

These helpers still need integration into the real SHA caller proofs, including
state preservation across their complete call lifecycles and the canonical
program bridge. They do not yet discharge all `sha_globals_ok` premises of the
existing jet theorems, and add no final equivalence to the published count.

## Isolated canonical secp normalization bridge

The next missing canonical-program bridge is now compiled outside the repository
in `/tmp/jet_secp_canonical_normalize.v`, with final exit 0 recorded in
`/tmp/jet-secp-canonical-helper-compile-final.log`. It contains seven complete
lemmas/theorems. Its `canonical_fe_normalize` ports the literal composition from
pinned `Programs/LibSecp256k1.hs:467–469`: subtraction from the field order,
projection rearrangement, then conditional selection of the original input or
subtracted payload. The field order is the actual literal from the pinned
Haskell library. No replacement mathematical function is used as the program.

The numeric bridge proves this program evaluates to x mod p for every Word256.
It then relates the existing nvz normalization model to the canonical program
through normalized limb uniqueness. Finally,
`eval_fe_normalize_var_against_canonical_program` transports the actual compiled
Clight execution/output/framing theorem for `secp256k1_fe_normalize_var` to those
canonical-program limbs. The helper keeps its existing <=2^60 input-limb bounds;
they are not silently treated as proved for the public jet.

The public `simplicity_fe_normalize` jet still needs complete `read_fe` /
`write_fe` byte/frame execution, representation and lifecycle proofs. This bridge
adds no registered jet equivalence until those are discharged. Failed scratch
attempts were localized to modulus spelling, placeholder inference, an opaque
constant's numeric rewrite, notation scope, required namespaces and tactic
branch scope. The final complete compiler exit, not any failed prefix, is the
verification evidence.

Both complete scratch sources are also preserved outside all audited repository
inputs at `/Users/brenorb/.codex/jet-proof-scratch/original-c/` for integration in
a later verified round. The currently running candidate audit has passed all
567 kernel modules and is evaluating the public assumption inventory. Resume
session `53393`; its log remains `/tmp/jet-next-canonical-candidate.log`.

## Reviewed candidate completed; final acceptance pending

The candidate log `/tmp/jet-next-canonical-candidate.log` finishes with
`candidate_audit_exit_status=0`. All 567 kernel modules, the public assumption
inventory, contract/definition generation, negative tests and four original-AST
regenerations passed. Its frozen input SHA-256 is
`fe314944ebc695177ae320275b540ba5b8611b06092f9ce50e8528c78903488c`.
Session `53393` is terminal and must not be restarted.

The actual diffs were inspected: all 3,331 old axiom records are identical;
only the two raw annex contracts and their composition lemma are added. The
inventory is now 3,334, with 1,683 closed results. Library-level axioms are
unchanged. All old printed theorem types and definitions are byte-for-byte
unchanged; the contract file has only two insertions, totaling 138 lines, for
three new types and five newly frozen definitions. The current annex definition
retains the nested missing-index/absent-annex distinction. The shift definitions
retain the literal recursive pair/projection programs reviewed against Haskell.
Coverage/negative-fixture and source diffs were also inspected.

The final run is now active in unified execution session `24260`, log
`/tmp/jet-next-canonical-final-accept.log`, using the exact same
proof/checker/target inputs and `check-jets.sh --accept` without update flags.
Do not change those inputs, commit, integrate or push until that actual run
finishes successfully. Markdown progress/receipt edits are outside the frozen
input fingerprint. Published coverage remains 319 pending this final run.

## Isolated actual secp byte/limb conversion execution

`/tmp/jet_secp_b32_exec.v` is now a completely compiled source, final exit 0 in
`/tmp/jet-secp-get-b32-exec-compile.log`. It is preserved outside the repository
at `/Users/brenorb/.codex/jet-proof-scratch/original-c/jet_secp_b32_exec.v`.
Its actual C helper contracts are `eval_fe_set_b32_from_initial_regions` and
`eval_fe_get_b32_from_initial_regions`. They use the existing symbolic executor's
Clight soundness and actual pure-function lookup table, not assumed execution.

The setter proves the precise int return for value<p, writes all five limbs and
retains the executor's outside-region memory framing. The getter proves the
actual void call, all 32 resulting bytes and that same framing. Their initial
region representations are explicit memory preconditions; caller setup still
has to construct them from the real frame/array contracts. They have not been
registered as final jet equivalences.

The byte fold bound proves any 32 bytes in [0,255] represent a value in
[0,2^256). It derives the <=2^60 unsigned-limb bounds used by the normalization
helper from the byte conversion result. A generic checked byte-region loader
connects the symbolic byte cells to actual Mint8unsigned loads; the getter's
closed output cell/checker facts and 52-bit input-limb bounds are also proved.
The earlier range mismatch was symbolic ofs+0, fixed by rewriting, not a stronger
premise. Inspection of later failed goals corrected a lambda/projection and an
automatically substituted offset. The final complete compilation is the evidence.

The pinned read_fe body normalizes if set_b32 returns zero; that validity return
is not the public jet's success/failure return. The write_fe body normalizes
again before conversion to bytes. The literal canonical program's idempotence
has therefore also been proved and compiled in
`/tmp/jet-secp-canonical-idempotence-compile.log` (exit 0), preserving all Word256
inputs including values>=p. The persistent canonical-normalization scratch file
now includes that additional lemma.

All these scratch proofs remain outside the frozen final acceptance inputs.
Final acceptance session `24260` is live; log
`/tmp/jet-next-canonical-final-accept.log`. No current-round commit or publication
has occurred. The remaining public fe_normalize obligations are initial region
construction, C read_fe/write_fe wrapper lifecycles, source-frame copy, final
output encoding/framing and linkage to the canonical program.

## Byte/limb initial-memory obligations discharged in isolated support

The current complete `/tmp/jet_secp_b32_exec.v` compiles with exit 0 in
`/tmp/jet-secp-b32-storage-compile-final.log`. It contains 42 checked
lemmas/theorems (previous complete prefix: 26). Its durable source copy is
`/Users/brenorb/.codex/jet-proof-scratch/original-c/jet_secp_b32_exec.v`.
These inputs are outside the running repository acceptance scope.

`set_b32_initial_rep_derived` constructs both initial symbolic regions from
ordinary memory facts: five writable aligned limb slots, 32 readable byte slots
with their initial loads, pointer bounds and distinct blocks. The output need
not have any initial value. `eval_fe_set_b32_from_storage` then derives the
actual Clight call, the exact validity return (`be_val bytes < feP`), output
limbs and outside-footprint framing. The bytes retain the entire 256-bit domain.

`get_b32_initial_rep_derived` constructs writable undefined byte slots and the
readable limb region from `fe_at`; writable limb permission implies the needed
readable permission. `eval_fe_get_b32_from_storage` derives the actual void
Clight call and exact big-endian byte loads. No helper execution or output fact
is added to either final initial-memory statement.

Remaining public-jet obligations are the actual `read_fe`/`write_fe` wrappers,
local allocation/free, read8s/write8s frame linkage, output encoding and the
canonical program bridge. These 42 results are auxiliary support; no secp jet
is newly registered, integrated or published.

At 2026-10-05 20:45:04 UTC, final acceptance session `24260` remains live, with
`coqchk` PID `39394` using approximately 100% CPU after 15:11. Its log still
ends at `== coqchk` and has no terminal status. Resume this exact run; do not
restart it or edit audited proof/checker/manifest/target inputs while active.
The audited input SHA-256 remains the reviewed candidate's `fe314944...`.
Current-round commits/publication remain pending actual acceptance.

## Actual read_fe/write_fe wrapper calls compiled outside acceptance scope

`/tmp/jet_secp_wrapper_run.v` now compiles with exit 0 in
`/tmp/jet-secp-read-fe-wrapper-compile-final.log` (nine completed results).
Its symbolic run uses the actual `f_read_fe`, allocates/frees the 32-byte local
buffer, calls original set-b32 and normalizer functions, and has three leaves.
The read event variables are explicitly derived from the initial input bits;
`eval_read_fe_from_initial_regions` applies the verified read8s oracle and
executor soundness to derive the real void Clight call. Its inputs are memory
representation, external-frame separation and the existing frame invariant.
It does not assume any helper call or output.

`/tmp/jet_secp_write_fe_wrapper.v` likewise compiles with exit 0 in
`/tmp/jet-secp-write-fe-wrapper-compile-final.log` (eight completed results).
It uses the actual `f_write_fe`, normalizer, get-b32 and verified write8s oracle.
The destination pointer is external to the symbolic regions, exactly as required
by the oracle; the local field region remains represented and writable. Both
normalizer branches execute, and oracle events are derived for the destination
frame without assumptions about the written byte values.

`eval_write_fe_from_initial_regions` derives the actual void Clight call, final
region representation, external frame invariant and memory framing. The write
invariant permits arbitrary inherited prefix bits, cursors and initial outputs
subject to the stated valid capacity; no canonical field-value restriction is
introduced merely to execute the wrapper.

Durable source copies are under
`/Users/brenorb/.codex/jet-proof-scratch/original-c/`. These 17 wrapper results
are auxiliary, outside this acceptance round and unregistered. Remaining work
is the numeric interpretation of their final states/event bytes, the canonical
field-normalization bridge, and the real public jet's by-value source-frame
copy and complete allocation/free/function boundary.

At 2026-10-05 20:59:41 UTC, the specific final acceptance session `24260` is
still live. All 567 kernel modules passed; assumption collection is running in
`coqc` PID `52992` (11:49, approximately 99% CPU). No final exit status exists.
The next atomic commit plan is prepared, but no current-round commit or push
may occur before that actual acceptance completes successfully.

## Initial bit-to-byte decoding bridge compiled

`/tmp/jet_secp_input_bytes.v` compiles with exit 0 in
`/tmp/jet-secp-input-bytes-compile-final.log` (seven completed results).
It proves that successive eight-bit MSB-first slices reconstruct the same
integer through the actual big-endian byte fold, gives each indexed byte as
`ifield bits (8*j) 8`, and derives byte bounds for every full input bit list.
This is the next numeric input bridge for the wrappers, not a new jet contract.
Its durable copy is under the same isolated scratch directory.

The printed types and assumptions of both completed wrapper calls were reviewed
in `/tmp/jet-secp-read-fe-review.log` and `/tmp/jet-secp-write-fe-review.log`
(both complete compilations, exit 0). They have exactly the six already recorded
axioms of `xfun_top_sound` and `orc_rd8_ok`/`orc_wr8_ok`: the inherited Coq
classical/extensionality context and CompCert external/assembly semantics.
Neither introduces a new axiom, helper-execution premise or output premise.

The main final acceptance now reports 567 kernel modules and 3,334 public
assumption records (1,683 closed) passed; public theorem contracts match the
reviewed snapshot. Its negative fixtures and final source/AST gates are still
running. Session `24260` remains live; require its final exit status before
committing/integration/publication.

## Final acceptance completed; atomic integration authorized

Session `24260` is terminal, exit 0, observed 2026-10-05 21:05:19 UTC.
`/tmp/jet-next-canonical-final-accept.log` reports all acceptance gates passed:
567 kernel modules, 3,334 results (1,683 closed), reviewed contracts/definitions,
negative tests, all four original-source ASTs and unchanged audited inputs.
Final snapshot-inclusive SHA-256:
`a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`.
The candidate/updating mode excludes its three generated snapshot files, so
its `fe314944...` hash differs by design; recomputing that mode still matches.
The earlier note expecting equality of those two mode hashes is superseded.

The next three atomic commits separate raw annex proof support, the reviewed
27-entry registration/specification gate, and acceptance/remaining-work docs.
Only this reviewed tree may be fast-forwarded to `feat/jet-equivalence` and
pushed to the user fork. All isolated scratch proofs remain outside this round.
The full goal remains unfinished: 187 header declarations are unregistered.
