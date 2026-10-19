# Consumer repair continuation (2026-10-09)

Local integration: signed commit `805cb19e` is now merged into
`feat/jet-equivalence`; integration-branch references below are historical.
Newer proof work is preserved separately in the checkout.

## Current status (authoritative)

The exact repaired candidate is now assembled on `codex/range-integration`.
All 149 reviewed file hashes and its complete proof-input fingerprint match
the passing full acceptance below. A durable copy of that run is retained as
`reconciled-accept.log`; integration details are in `RECONCILIATION.json`.
The subsequent checkout receipt describes the earlier main checkout, including
its unrelated unregistered experiment, rather than this isolated branch.

The reconciled candidate full `check-jets.sh --accept` run **54683 passes with
exit 0**. Its log is `/tmp/jet-range-consumer.RbIhbg/reconciled-accept.log`:
build, 603 kernel modules, 3583 assumption records (1860 closed), reviewed
contract/definition snapshots, negative gates and all four ASTs pass. Fingerprint:
`dccfcbcd42e6b7c419992597362ebf4a2c2df407769183a217a27599718e8f07`.
After HEAD/old/new hash checks, all 149 integration files were copied into the
checkout with exact final candidate hashes; unrelated user files were preserved.
Coverage remains 349/533. No commit or push is claimed.

Actual-checkout verification **24458 passes with exit 0**:
`check-jets.sh --accept`, log `/tmp/jet-range-integrated-accept.log`.
Its fingerprint is `a4a8c23458e98da8a41e9fb3c8ae644400ed081652b238147387150d7e02fb37`.
The preserved untracked math experiment remains a fingerprint input but is not
registered or included in the proof build. All 603 kernel modules, assumption
and contract gates, negative tests and four AST comparisons pass. The final
fingerprint was rechecked against the checkout and still matches; this separate
receipt releases the actual-checkout input freeze. Candidate acceptance is not
used as this run's receipt.

All 44 repaired-module kernel checks, reconciled predicate checks, complete
3,583-result assumption comparison and three concrete/domain review modules
are complete. Integration coverage remains 349/533; the repaired proof
inputs match the reviewed candidate. `RECONCILIATION.json` guards 149 prospective integration
inputs against `cafb9b31`; the repaired integration is prepared on its own
branch. Earlier signing failures describe the prior checkout attempt.

## Historical receipt journal

Older live-handle instructions below describe their time of observation;
they are superseded by the current status above. Do not restart those runs.

The archived candidate is still unaccepted. Do not apply its snapshots to the
accepted tree or count its helper checks as additional jet coverage.

Fresh dependency rebuild: `/tmp/jet-range-consumer.RbIhbg`, reconstructed from
candidate commit `00536113eb285b109f00c28a0fd22de66b05ec35` using `git archive`.
The original candidate worktree's objects use OCaml 4.14.1 and cannot be loaded
by the current Nix Coq 8.17.1/OCaml 4.14.4 compiler. This scratch rebuild uses
the current compiler and existing matching CompCert/VST dependencies.

Session **54357** was intentionally terminated (exit 143): the wrapper prepends
`all` to supplied targets, so the outer target and recursive `real-all` launched
duplicate compilers writing `jet_exec.vo`. The identified scratch processes
were stopped; the unrelated SHA kernel check was not stopped. Session **95958**
rebuilt only the original failing target and its dependency closure, then
terminated with exit 2 at the reproduced `jet_full_multiply8_layout.v:122`
failure. No stale objects were used for the repairs below.

```sh
cd /tmp/jet-range-consumer.RbIhbg/Coq
PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH \
  make -f JetMakefile -j2 C/jet_full_multiply8_layout.vo
```

A separate scratch copy at
`/tmp/jet-range-consumer.RbIhbg/jet_full_multiply8_layout.v` changes only the
initial `Hout` destructuring: remove the old top-level `HD` field. The revised
`write_frame_at` puts separation inside each accessed word's contract; its
top-level fields are now `HDbase`, frame fields, edge/cursor bounds, `PD`, and
`HW`. The proof's preservation step already has the complete load and
permission transport hypotheses. This edit adds no premise or weaker conclusion.
The corrected separate copy now compiles with exit 0 (`--coqc`, session 52435).
Both edits below were then applied to the isolated `Coq/C` tree with normal
file-editing tools. A direct Makefile build of both `.vo` targets completes
with exit 0 (session 93067), including the complete public full-multiply
specification, context and guarantee declarations. No accepted source is edited.

Then repair the remaining consumer chain, perform independent kernel checks,
review contract/definition/assumption differences, and run full acceptance.
The old 20-patch archive remains unchanged and reproducible.

`consumer-repair.patch` preserves two **compiled and kernel-checked** edits against the
exact archived candidate: the full-multiply destructuring correction and
`jet_output_cells_step`'s writable-continuation proof. The latter carries each
word's range separation into the new continuation contract and derives the
outside-metadata load condition from that range rather than assuming distinct
blocks. No theorem statement is changed. `git apply --check` passes against the
reconstructed candidate; that is patch applicability, not Coq verification.
Its second scratch source is `/tmp/jet-range-consumer.RbIhbg/jet_output_cells_step.v`;
whole-file `--coqc` completed with exit 0 before rebuilding it in namespace `C`.
Patch SHA-256: `44faf44be58bb0845eeb8185783e8acafdf28c8447c0a7cda170b4a7539fda8a`.

Independent full-chain kernel checking of `C.jet_full_multiply8_layout` and
`C.jet_output_cells_step` completed with exit 0 (session **43206**); its log is
`/tmp/jet-range-consumer.RbIhbg/consumer-kernel.log`: 15 existing allowlisted
library axioms, no unsafe/type-in-type/assumed-positivity flags.
Full consumer build, snapshot review and independent acceptance remain open.

The next targeted `C/jet_frame_inv.vo` build terminated with exit 2 at
`jet_bitcoin_effects.v:56` (session 80387). Its actual failing context revealed
the same old top-level separation destructuring. `effects-repair.patch`
preserves the subsequent complete repair; its SHA-256 is
`66b083a2ca09588323bb2773351a7a52465ab9fb0de9653333a8fab16456efce`.
Both write-effect composition and writable continuation derive range separation
from the initial accessed-word facts. Composition explicitly handles
`n1 + n2 = 0` through same-cursor prefix transitivity; it does not require
positive capacity or fabricate a head-word separation fact for an empty frame.
All original theorem/definition statements are retained.

The complete scratch effects source compiled with exit 0 and was applied to
the isolated `Coq/C` tree. Its `C` module then compiled in session 75822, whose
build next failed at `jet_frame_inv.v:47`: `fext_bd` destructures the old
contract shape. The following `finv_init`, `write_frame_at_le`, `finv_wframe`
and `finv_write` also visibly use the old separation interface. Repair those
from the actual per-word ranges, preserving empty-frame behavior and the
restricted `fext` memory/permission observations. Do not replace the latter
with a stronger assumed global write-effect contract.

Independent whole-chain checking of `C.jet_bitcoin_effects` completed with
exit 0 (session **10143**), log `/tmp/jet-range-consumer.RbIhbg/effects-kernel.log`:
15 allowlisted library axioms, no unsafe kernel flags. The separate SHA
input/running-adapter kernel check also completed with exit 0 (session **5190**).
The accepted-tree audited fingerprint remains
`6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`:
these repairs have not modified its proofs, registry or snapshots.

`frame-invariant-repair.patch` repairs all affected invariant consumers without
changing any text outside their `Proof`/`Qed` blocks. Patch SHA-256:
`34287957ab1efdcaf5cb7ca49deb13e85bfaa23bdf4aef0e66a0486fd87b92a9`.
The full scratch file and rebuilt `C.jet_frame_inv` compile with exit 0; its
independent whole-chain kernel check passes with exit 0 (session 13757), log
`/tmp/jet-range-consumer.RbIhbg/frame-invariant-kernel.log`, with 15 allowlisted
library axioms and no unsafe flags. `fext`, `weffE`, `finv`, theorem statements
and their restricted memory observations remain unchanged. Empty composition
uses same-cursor prefix transitivity; positive composition derives separation
from the appropriate original word.

The next secp consumer build failed at `jet_secp_frame.v:559`, again due to
old writable-contract destructuring. `secp-frame-repair.patch` removes only
those stale fields and compiles the complete module with exit 0 (session 96308).
Its reverse applicability check passes on the repaired scratch tree. SHA-256:
`6e274def356dbdfdad75cd69c44e55d1ec9718d12ae54e18e19dedb9140e4307`.
Kernel checking completed with exit 0 (session **11614**), log
`/tmp/jet-range-consumer.RbIhbg/secp-frame-kernel.log`.

The copying-consumer build terminated with exit 2 (session 81857), exposing
`jet_copyBits_short_cells.v:140`. This is not only destructuring:
`eval_copyBits_short` in `jet_copyBits_short_exec.v:47` still requires
`bd <> bw`, which the new frame domain correctly does not imply. Generalize
that execution/helper chain to the actual metadata/word byte-range separation,
derive it from `write_frame_at_head_separate`, and preserve every output,
cursor, framing and permission conclusion. Do not restore distinct blocks as
a new public premise. The following short-copy continuation repairs that first
execution chain without restoring distinct blocks.

`short-copy-repair.patch` covers six modules: partial-tail/left execution,
right execution, short wrapper execution, short cell output, aligned-loop
execution, and aligned short cell output. Patch SHA-256:
`12329c02dfc355a511ff4631b10596eb6e2e86c9174e91cb07c6c4eec7cb4ac2`.
All six compile on the isolated candidate. The two cell-level initial-only
contracts retain their exact statements and derive separation from
`write_frame_at_head_separate`. The raw/internal helper statements weaken only
`bd <> bw` to the corresponding metadata-versus-word range disjunction; all
other non-proof text is unchanged, apart from two explicit module imports.
Actual C, output values, cursor updates, outside loads and permission/valid-block
conclusions are preserved. The wrapper derives its word-load preservation
across the real cursor update from that range, not from an output assumption.

Independent whole-chain kernel checking of `C.jet_copyBits_short_cells` and
`C.jet_copyBits_aligned_short` passes with exit 0 (session 73094), log
`/tmp/jet-range-consumer.RbIhbg/short-copy-kernel.log`: 15 allowlisted library
axioms and no unsafe flags. Per-result assumption printing of
`eval_copyBits_short_layout` and `eval_copyBits_aligned_short_layout` completes
with exit 0 (session 6204); their six axiom names match their existing recorded
sets. No extra libc premise was introduced. The patch's reverse applicability
check passes on the repaired candidate, and original copies match the archived
candidate commit byte-for-byte.

The next targeted small-copy consumer build terminates with exit 2 (session
55706) at `jet_copyBits_aligned_crossing.v:146`: source-word crossing still
feeds the old `bd <> bw` interface in its aligned helper chain. Generalize
`eval_copy_helper_aligned_crossing` and derive its metadata/word separation
from the initial write frame, while retaining the separate existing
input-word/output-word separation needed after writes. Destination-word
crossings, memcpy paths, other consumers and full acceptance remain open.
No processes from this short-copy cycle are left running.

## Source-word crossing continuation

`source-crossing-repair.patch` repairs four further modules: aligned crossing
helper/cell output and partial crossing helper/cell output. SHA-256:
`0360eacd3d3c2d95476488782a6d3a77a6029c331a5a1efe21c84acac4286e3a`.
The aligned raw helper's actual name is `eval_copy_helper_aligned_full`.
Both raw helpers weaken only metadata/data block inequality to separation of
the touched word's byte range from the metadata record. The cell contracts
retain their statements and derive that separation from the initial frame.
Existing source/output separation premises, real C calls, output values,
cursor updates, outside loads, permissions and valid-block conclusions remain.
Metadata loads are preserved across the actual stores, using the shared range
lemma; preservation after the cursor store is likewise proved by ranges.

All four whole modules compile. Partial crossing compilation completes with
exit 0 (session 67471). Independent whole-chain checking of
`C.jet_copyBits_aligned_crossing` and `C.jet_copyBits_partial_crossing_cells`
completes with exit 0 (session 7069), log
`/tmp/jet-range-consumer.RbIhbg/source-crossing-kernel.log`: 15 inherited
allowlisted library axioms, no type-in-type, unsafe fixpoints or assumed
positivity. A comparison against `00536113` verifies unchanged non-proof text
except the two documented premise weakenings and explicit imports. Scratch
original copies contain one extra terminal newline; the archived patch omits
those artificial end-of-file changes. Reverse applicability passes.

The next direct target `C/jet_copyBits_small_full.vo` terminates with exit 2
(session 8342), at `jet_copyBits_two_words_left_cells.v:110`: stale `Hwrite`
destructuring loses `Hwords`. Its raw `eval_copy_helper_two_left` also still
requires `bd <> bw`. Repair the chain using separation for **both** destination
words, deriving the lower word's range from the original capacity predicate.
Do not simply reuse head-word separation for the lower word or restore block
inequality. Two-destination-word consumers, memcpy paths and full acceptance
remain open. No process from this continuation remains live. This is support
for the range candidate, not newly accepted jet coverage; the accepted input
fingerprint remains `6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`.

## Two-destination-word left-copy continuation

`two-left-repair.patch` repairs the raw execution helper and its cell contract.
SHA-256: `808efad6ddb3ace3921b019bd59a440db672c49a298cb5565aa6b14150b68c80`.
The raw helper replaces `bd <> bw` by the conjunction of metadata separation
for the head word and lower word. This is a weaker premise: distinct blocks
imply both disjunctions, but distinct blocks are not necessary. The cell-level
theorem retains its complete statement. It derives head separation using the
shared lemma, and lower separation from capacity at index `cursor mod 64`.
The lower address is rewritten with `copy_partial_cross_write_address`.
Actual stores SC/SL/SP touch the head, and SF touches the lower word; the proof
uses the appropriate separation for each. Both loads are preserved through the
real cursor update. No execution/output premise or libc premise is added.

Both whole modules freshly compile with exit 0 (session 68869). Independent
whole-chain kernel checking of `C.jet_copyBits_two_words_left_cells` passes
with exit 0 (session 20458), log
`/tmp/jet-range-consumer.RbIhbg/two-left-kernel.log`: 15 inherited allowlisted
library axioms and no unsafe flags. Printing assumptions for
`eval_copyBits_two_left_layout` completes with exit 0 (session 47601); its six
axiom names match the existing recorded set. Exact original copies match
`00536113` byte-for-byte. Non-proof comparison permits only the documented
raw-premise weakening and import; cell statement/conclusions are unchanged.
Reverse applicability passes. Accepted inputs and coverage remain unchanged.

The next direct small-copy build terminates with exit 2, revealing parallel
failures at `jet_copyBits_two_words_right_short_cells.v:85` and
`jet_copyBits_two_words_right_full_cells.v:108`. Both still destruct the old
write-frame tuple and feed distinct-block premises to their raw helpers.
Apply the same two-word range reasoning to these chains, respecting the
different head/lower store sequences and source preservation premises.
No process from this left-copy continuation remains running.

## Two-destination-word right-copy continuation

`two-right-repair.patch` repairs four modules: short/full raw helpers and their
cell contracts. SHA-256:
`e94ecc83a641aa791bcac1613dffd52acd045af9cd34370e831c0cbb506af68d`.
The helper premises weaken block inequality to the head/lower metadata-range
conjunction; both cell contracts retain their full statements. Initial frame
capacity supplies both separations. Short copying uses SC/SP at the head and
SF at the lower word. Full copying uses SC/SP at the head and SI/SF at the
lower word. Each metadata-preservation rewrite uses its actual store's range.
Existing source-load preservation premises and all conclusions are retained.

The first full-helper compilation timed out at outside-load proof line 155
(session 54951). Broad `intuition lia` split the new unrelated separation
disjunctions. Explicit three-case elimination of `Houtside` fixes the cause
without increasing the timeout or weakening the result. All four whole modules
then compile, and `jet_copyBits_small_layout` also compiles (session 83230).
The overall requested small-full target is still incomplete, not a successful
build: it terminates with exit 2 at `jet_copyBits_memcpy_cells.v:75`.

Independent whole-chain kernel checking of both right-copy cell modules passes
with exit 0 (session 89221), log
`/tmp/jet-range-consumer.RbIhbg/two-right-kernel.log`: inherited allowlisted
axioms and no unsafe flags. Assumption printing for both cell contracts passes
with exit 0 (session 97149); each six-name set matches its recorded set.
Original copies exactly match `00536113`. Non-proof comparisons confirm only
the documented raw-premise weakening/imports; cell statements are unchanged.
Patch reverse applicability passes. Accepted input fingerprint is unchanged.

Next repair `jet_copyBits_memcpy_helper` and `jet_copyBits_memcpy_cells`:
aligned copying needs head-word metadata separation; equal-shift copying also
needs lower-word separation. Derive metadata preservation from the existing
memcpy outside-load effect, and derive separation from the initial writable
frame. Keep the explicit `memcpy_model` premise: this continuation is not a
proof of libc. Wide consumers and full candidate acceptance remain open.
All sessions from this continuation are terminal; no kernel/build process is
left running.

## Small memcpy continuation

`memcpy-small-repair.patch` repairs both memcpy paths in the helper and cell
modules. SHA-256:
`ec538852f1309751cfe03e180de7aa3a5a2d12963cfcfd7bc2a5d8c5dc5305f3`.
The aligned raw helper requires head-word metadata range separation, and the
equal-shift raw helper requires both head/lower separation. Cell statements
remain unchanged and derive these ranges from the writable capacity predicate.
The existing memcpy outside-load effect proves metadata-load preservation;
equal-shift copying also preserves metadata across its two actual head-word
stores. Actual cursor-update preservation uses the appropriate word range.
Explicit `memcpy_model`, source/output separation and all conclusions remain.

The complete `C/jet_copyBits_small_full.vo` target freshly compiles with exit 0
(session 99167). Independent whole-chain kernel checking of
`C.jet_copyBits_small_full` passes with exit 0 (session 33503), log
`/tmp/jet-range-consumer.RbIhbg/memcpy-small-kernel.log`: inherited allowlisted
axioms, no unsafe flags. Assumption printing of the two memcpy cell contracts
and combined `eval_copyBits_small_layout` completes with exit 0 (session 92249);
all three six-name sets match their existing records. The initial assumption
probe failed because importing the combined module does not re-export helper
names; explicitly importing the cell module fixes the probe. Original copies
match `00536113` exactly; non-proof comparison permits only documented helper
premise weakenings/import. Patch reverse applicability passes.

Direct `make -f JetMakefile -j2 all` terminates with exit 2 (session 62895),
after compiling many further consumers, at
`jet_write_wide_mixed_sequence.v:77`. Its old `Hfw` variable is now writable
metadata access, not block inequality. Both `frame_output_cells_prefix_preserved`
and `write_prefix_at_chain` now need indexed word/metadata range separation.
Correct the original `HW` tuple destructuring, derive the per-cell premise from
its capacity predicate (using encoded-width bounds), and handle the chain's
zero-tail case appropriately. Do not restore a global distinct-block premise.
Wide consumers and full acceptance remain open. Accepted coverage and input
fingerprint are unchanged. All sessions from this continuation are terminal.

## Mixed-width sequence continuation

`mixed-sequence-repair.patch` changes only the proof of
`write_wide_mixed_run_layout`; all definitions and theorem statements remain
unchanged. SHA-256:
`3d1b65304bab2182d69ed605edffb713f8845f470fb64dd98c890cf74491a58f`.
Head-word separation comes from the original positive total capacity. The
indexed premise for earlier output cells comes from that same capacity,
after proving each encoded index is less than the current writer's width via
`encode_word_length` and `wide_bits_pow`. Prefix composition uses head-word
separation, not a global block inequality. No extra premise is introduced.

The whole module compiles with exit 0 (session 47660). Independent whole-chain
kernel checking passes with exit 0 (session 87864), log
`/tmp/jet-range-consumer.RbIhbg/mixed-sequence-kernel.log`: 15 inherited
allowlisted axioms and no unsafe flags. Assumption printing completes with
exit 0 (session 69551); the six-name set matches its existing record. Exact
original and non-proof comparisons pass, as does reverse patch applicability.
Accepted input fingerprint is unchanged; no additional coverage is claimed.

The broader direct `make -f JetMakefile -j2 all` (session **83028**) reports the
next failure at `jet_empty_buffer_segment.v:23`, but was still waiting for its
other worker at the last poll. **Poll that existing session; do not restart
the build or assume it is terminal from the error alone.** The independent
kernel and assumption sessions are terminal. The next file has old writable
tuple destructuring in both padding and segment proofs; padding must preserve
the per-word separation and derive metadata-range exclusion for each data
load. Later `HSkipMem by auto` uses also need genuine range evidence. Inspect
those obligations before changing the proof. Full candidate acceptance remains
open.

## Empty-buffer padding continuation

`empty-buffer-repair.patch` changes only proof bodies in
`jet_empty_buffer_segment.v`; definitions and theorem statements are unchanged.
SHA-256: `97bed494f1745618dca538bd4ab83bc002540c86247a5b9a46ad94cfababda3c`.
Padding continuation shifts the original capacity index by `n`, retains its
per-word metadata separation and derives the exclusion needed for its backing
load. The segment derives head-word separation from its positive original
capacity and uses it for real skipBits preservation. The old generic prefix
helper demanded preservation of every data-block load, which cannot be derived
from head-word separation. A direct prefix proof preserves exactly the head
load and its existing outside-bit equality, retaining the full conclusion.

First compilation exposed that overly strong helper use at line 91 (session
99732); the corrected whole module compiles with exit 0 (session 58967).
Independent whole-chain kernel checking passes with exit 0 (session 72864), log
`/tmp/jet-range-consumer.RbIhbg/empty-buffer-kernel.log`, with inherited
allowlisted axioms and no unsafe flags. Assumption printing passes with exit 0
(session 11977): the padding lemma's four-name and segment's six-name sets match
existing records. Exact original/non-proof comparisons and reverse patch
applicability pass. Accepted inputs and coverage remain unchanged.

The previous broader build, session 83028, is now confirmed terminal with exit
2. A subsequent whole build, session 54416, also terminates with exit 2, after
many additional arithmetic/layout consumers compile. Its next failure is
`jet_write64_then32s_layout.v:55`: the same old `Hfw` destructuring and indexed
prefix preservation seen in mixed-width sequencing. Repair its head/indexed
separation from the original capacity, as in `mixed-sequence-repair.patch`.
Retain its separate input-array non-aliasing premises and all calls/outputs.
No process from this continuation remains live; full acceptance remains open.

## write64 then uint32-array continuation

`write64-array-repair.patch` changes only the proof of
`eval_write64_then32s_layout`. SHA-256:
`8adff42cffcdde401068904fcbc06ada90379b17c5b3e79b18a447c6b32e09b5`.
Head-word separation comes from positive total capacity; each earlier encoded
cell's separation comes from the same capacity after the encoded length is
proved to be 64. Input-array separation premises, actual calls, output/cursor
and memory guarantees are unchanged. Whole compilation succeeds with exit 0
(session 51127). Independent kernel checking succeeds with exit 0 (session
60894), log `/tmp/jet-range-consumer.RbIhbg/write64-array-kernel.log`, with
inherited allowlisted axioms and no unsafe flags. Assumption printing succeeds
with exit 0 (session 95033); the six-name set matches its existing record.
Exact original/non-proof comparisons and reverse applicability pass. Accepted
inputs/coverage remain unchanged.

The next whole build is confirmed terminal with exit 2 (session 29940).
It reports timeouts at `jet_parse_sequence_writer.v:64` (destructing the tag
and converting an encoded output) and `jet_rotate_word_controls.v:46`.
These are newly reached leaves, not evidence the whole candidate compiles.
Inspect exact goals and isolate conversion/reduction; do not indiscriminately
raise timeouts or unfold generated programs. No process from this continuation
remains live. Snapshot/domain review and full acceptance remain open.

## Timeout continuation: parse-sequence and rotation controls

`timeout-repair.patch` contains two proof-only repairs and corrected rotation
case-count comments. SHA-256:
`37184753007548f95db698c092a8b8f1a369977729741afb2c3107faccc8bb7a`.
Definitions, theorem statements and timeout settings remain unchanged.
The exact parse-sequence leaf was inspected with `Show` in a stopped coqtop
prefix, without any admission. Its carry-pair encoding is rewritten using a
proved local equality with an abstract Word16, avoiding case splitting the tag
inside the huge concrete decoded payload. The full module compiles (session
89643) and passes independent kernel checking (session 67841), exit 0, log
`/tmp/jet-range-consumer.RbIhbg/parse-writer-kernel.log`, with inherited
allowlisted axioms and no unsafe flags.

Canonical rotation uses only six relevant controls at width32 and seven at
width64 (including the final SingleV step). Leave the two/one unused high bits
symbolic instead of splitting them: this reduces the checks from 256 to 64/128
cases, with symbolic payloads and the original bounded deadlines. The exact
saved module freshly compiles with exit 0 (session 9438). Assumption printing
(session 1217) passes: both rotation equalities remain closed, and the writer's
six-name set matches its existing record. Exact originals, non-proof comparison
(excluding comments) and reverse patch applicability pass. Accepted audited
inputs are unchanged; these changes have no new jet registration.

Independent rotation kernel checking completes with exit 0 (session 32778),
log `/tmp/jet-range-consumer.RbIhbg/rotate-controls-kernel.log`: 15 inherited
allowlisted axioms and no unsafe flags. The broader whole build is **still
running** (session **29450**) and has advanced through parse-sequence, rotation,
Bitcoin support, wide copy support and secp support consumers. Process inspection
confirmed active CPU use, not a stalled or stopped handle. Poll that exact
session, do not restart or claim completion from compiled prefixes. Source
inspection identifies the next likely stale frame-tuple consumer in
`jet_bitcoin_write32s_layout.v:69,114,133`; wait for the build's exact failure
before applying the same indexed/head separation reasoning. No edit to that
module has been made. Full range-candidate acceptance remains open.

## Fill-shift16 timeout continuation

The broader build session 29450 is now confirmed terminal with exit 2, exposing
`jet_shift16_with_spec.v:23`, its single 64-case reduction sentence. A stopped
coqtop prefix inspects all remaining cases after measuring the first case:
0.189 seconds, successfully checked. No admission is used. The range-selector
syntax is separately verified on a complete three-goal proof. Split the 64
cases into four sixteen-case sentences under the original ten-second deadline.
The symbolic payload bits, literal specification and theorem are unchanged.

`shift16-fill-repair.patch` SHA-256:
`2c324a2012960296a6b54156fd7c3bebc4d36f5159a7fef675954183a37cf97c`.
The whole module freshly compiles with exit 0 (session 35773). Assumption
printing passes and remains closed under the global context, matching its
existing record. Exact original/non-proof comparison and reverse applicability
pass; definitions, statements and deadlines are unchanged.

Its independent kernel check completes with exit 0 (session 95431), log
`/tmp/jet-range-consumer.RbIhbg/shift16-fill-kernel.log`, with inherited
allowlisted axioms and no unsafe flags. No process remains live. A subsequent
whole build, session 54916, is confirmed terminal with exit 2. The next failures
are `jet_shift32_with_spec.v:21` (one sentence expands all fill/direction and
eight control bits into 1,024 goals) and `jet_shift64_with_spec.v:88` (Qed for
its first split helper). The 32-bit file already batches reductions in groups
of eight; its failure is earlier case generation, not that reduction tactic.
The 64-bit failure is kernel/proof-term finalization, not an unfinished tactic
leaf. Diagnose these separately, avoiding indiscriminate deadline increases.
Neither source has been edited in this continuation. The likely Bitcoin tuple
consumer has not yet been reached. Accepted inputs/coverage are unchanged.

## Wider fill-shift continuation

`wide-fill-repair.patch` SHA-256:
`52966720d567d6999efa1a837f5666fd0cac2e8f17c11811cd0bb758ed0fccbe`.
The 32-bit case-generation failure is fixed by separate bounded sentences for
fill/direction, amount structure and each control bit. All 1,024 cases are
still checked in the existing eight-case reduction batches. Whole compilation
passes with exit 0 (session 71107), including the existing bounded kernel
finalization measured at 18.188 seconds. Its bridge remains closed under the
global context (assumption printing session 4918, exit 0).

For width64, an isolated complete first-helper probe measures Qed at 12.861
seconds (session 66877, exit 0), confirming that the ten-second default cannot
finish the kernel check. Only the four 256-case helper Qed steps now have a
thirty-second bound, immediately restoring ten-second tactic limits. This is
bounded actual kernel checking, not an unsafe cast/check bypass. No statement,
definition, control case or payload domain is changed. The full-module build
(session 11289) now completes with exit 0; all four kernel finalizations pass
at 11.952, 11.657, 11.789 and 10.684 seconds.

Independent width32 kernel checking completes with exit 0 (session 35212),
log `/tmp/jet-range-consumer.RbIhbg/shift32-fill-kernel.log`, with inherited
allowlisted axioms and no unsafe flags. Width64 independent
whole-module kernel checking is now running (session **81440**), log
`/tmp/jet-range-consumer.RbIhbg/shift64-fill-kernel.log`. Poll those handles;
do not restart. Exact originals and non-proof comparisons (accounting for the
timeout-reset commands), reverse patch applicability and accepted fingerprint
checks pass. The preserved patch is a candidate continuation, not acceptance.
The next whole build is now running (session **35650**) after both sources
compile. Poll its handle. The Bitcoin tuple consumer remains unrepaired/not
yet reached.

## Bitcoin array-write continuation

Both previously live handles are now terminal: width64 kernel session 81440
passes with exit 0, and whole-build session 35650 fails with exit 2 at
`jet_bitcoin_write32s_layout.v:114`. Its old tuple destruct incorrectly names
cursor-field writable access `Hfw` and tries to use it as word separation.

`bitcoin-array-repair.patch` SHA-256:
`236ddecad0b90f026261324ba36fff015f6c1d8a861c47a2346ad15872b89a13`.
The repair derives indexed separation for each of the first 32 encoded cells
from the initial frame capacity, and head separation for prefix composition.
It retains all array/source preservation, execution and final-memory facts.
All definitions and theorem statements compare unchanged against the exact
candidate source; reverse patch applicability passes. Whole-module compilation
passes with exit 0 (session 80102). Independent whole-chain kernel checking
passes with exit 0 (session 59742), log
`/tmp/jet-range-consumer.RbIhbg/bitcoin-array-kernel.log`.
This is candidate support, not acceptance or additional registered coverage.

## Wide-copy helper continuation

Whole-build session 3697 is terminal with exit 2, stopping at
`jet_copyBits_wide_helper.v:63`. Its `wh_bounds` lemma retained the obsolete
block-distinctness claim. `wh_bounds` now contains only the actual numerical
bounds. A new `wh_metadata_range` derives complete output-interval separation
from the first/last word predicates and the existing 65--128-bit bound: the
head and bottom word addresses differ by at most 16 bytes, so a 16-byte frame
record cannot fit between them without overlap. No block inequality is added.

The helper's actual stores and memcpy tail preserve the metadata via those
derived ranges. The wrapper's cursor store preserves each actual encoded
output word and the prefix word via indexed initial capacity; it no longer
claims every possible load in the output block is preserved.
The public helper/wrapper execution theorem statements and the wide-prefix
statement are unchanged. The explicit `memcpy_model` premise remains.

`wide-copy-helper-repair.patch` SHA-256:
`5960322b8d73bf9d801228288711cde66cb56978ef6cdc56f8cf6ad82acf53c9`.
Whole compilation passes with exit 0 (session 8835), and reverse applicability
and the exact unchanged execution-statement checks pass. Independent whole-chain
kernel checking passes with exit 0 (session 32228), log
`/tmp/jet-range-consumer.RbIhbg/wide-copy-helper-kernel.log`.
Assumption printing of the range lemma, both execution results, Bitcoin array
execution and all five width64 complement bridges passes (session 64657).
The range result uses four inherited assumptions; both execution results and
Bitcoin array execution retain the six existing assumptions. All five width64
bridges remain closed under the global context. The accepted input hash remains
`6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`.

Neither this helper nor a checked candidate prefix is additional acceptance.

The subsequent whole candidate build is running as session **39742** after
the helper kernel check completed. Poll this exact handle before further
consumer edits; no concurrent audit or target compiler remains live.
Latest output reports `jet_bitcoin_indexed_scalar.v:281`: "Not the right number
of missing arguments (expected 0)." The handle has not yet returned terminal
status because the other make worker is finishing. Inspect the actual tactic
and goal after polling that handle; do not assume this is another range tuple.

## Indexed scalar continuation

Build session 39742 is terminal with exit 2. A stopped, uncompiled coqtop
prefix in `indexed_scalar_goal.v` inspects the actual outstanding goals at
the reported line: an unintended `0 <= ?i < 1 + wide_bits s` obligation precedes
the intended existential conclusion. The old tuple pattern at line 146
destructs the capacity function as though it were an extra conjunction;
Coq introduces an index evar and its range premise. Correct the tuple arity,
not the final existential tactic. No additional premise or admission is used.

`indexed-scalar-repair.patch` SHA-256:
`c7874014ef4fe4e7bdca73eada489a0370c04b766fb952dfc4cd8a228c29e9c5`.
Whole-module compilation passes with exit 0 (session 71630). All definitions
and theorem statements compare unchanged; reverse applicability passes.
Independent whole-chain kernel checking passes with exit 0 (session 12745), log
`/tmp/jet-range-consumer.RbIhbg/indexed-scalar-kernel.log`.
Accepted inputs remain unchanged; full range-candidate acceptance stays open.

Assumption printing completes with exit 0 (session 35503) for both
`bitcoin_indexed_scalar_mid` and `bitcoin_indexed_scalar_local`: only the six
inherited classical/extensionality/CompCert semantics assumptions occur.
These support results have no direct accepted snapshot records; complete
downstream registered-chain and full snapshot review still remain necessary.

The subsequent whole candidate build is live as session **87615** after the
indexed-scalar kernel check completed. Poll that handle before consumer edits.

## Input-value and indexed-pointer continuation

Whole-build session 87615 is terminal with exit 2. It reaches the same final
existential error in `jet_bitcoin_input_value_local.v:234` and
`jet_bitcoin_indexed_ptr.v:270`. Both retain the exact earlier stale tuple
pattern, destructing the capacity function as an extra conjunction. Correct
only those two tuple patterns. Both whole modules compile with exit 0 (session
25240); all definitions and theorem statements compare unchanged against the
exact archived candidate, and reverse applicability passes.

`indexed-consumers-repair.patch` SHA-256:
`9ee8d6513756aeab63ffdeee05d1a7db1f0cb5336bd8a9be51415104aa73cb22`.
Independent combined whole-chain kernel checking passes with exit 0 (session 9639),
log `/tmp/jet-range-consumer.RbIhbg/indexed-consumers-kernel.log`.
Assumption printing of `bitcoin_input_value_local_spec` and
`bitcoin_indexed_ptr_local` passes with exit 0 (session 6686), retaining only
the six inherited assumptions. The accepted input fingerprint
remains unchanged. Full candidate integration/acceptance is still open.

## Value/hash sequencing proof continuation

Kernel session 9639 was observed live at 99.3% CPU and then completed with exit
0; it was not restarted. `jet_bitcoin_vh_hash_prep.v` has a scratch-only proof
repair to `write_cells_seq`: use indexed capacity for written cells, derive
head separation for positive capacity, and compose prefix equality directly
when both lengths are zero. All premises and conclusions are unchanged.

The exact repaired lemma is compiled in the complete minimal module
`/tmp/jet-range-consumer.RbIhbg/vh_sequence_probe.v`, exit 0. The first probe
failed because `C.jet_constant_layout` was not imported; importing the actual
owner of `frame_output_cells_preserved` fixes it. No admission is used.
The original whole value/hash module is not yet verified. The pending repair
is preserved as `vh-sequence-repair.patch`, SHA-256
`d23efb67954f1da9ec1159dd36953707fc0c96b9e9567050d61f370004a944cb`.
Reverse applicability passes; all definitions/statements compare unchanged,
and the checked probe lemma exactly matches the repaired lemma. An initial
patch serialization trimmed the final blank context line and was rejected;
restoring it fixes the archive, not the proof. This archive is explicitly
lemma-checked only, not whole-module verified or accepted.
Whole candidate build session **72972** is now running after the preceding
kernel check completed. Poll this handle; do not start duplicate compilers.

Session 72972 subsequently terminates with exit 2 at
`jet_bitcoin_tappath_local.v:473`, the final existential tactic. Inspection
shows the identical stale tuple at line 276 (`HDW [PD HWords]`), with `HDW`
unused thereafter. The next concrete repair is that tuple's arity, followed
by whole-module compilation and kernel checking. No tappath edit is made yet.
The value/hash whole module was not reached before this stop.

## Tappath continuation

Correct only the stale frame tuple at `jet_bitcoin_tappath_local.v:276`.
Whole-module compilation passes with exit 0 (session 74934); all definitions
and theorem statements compare unchanged, and reverse applicability passes.
`tappath-repair.patch` SHA-256:
`26083a0d88dc53798ccffb40c5ff8d3dc2fa62893ff2febabc98c1af5ec0397f`.
Independent whole-chain kernel checking passes with exit 0 (session 53647), log
`/tmp/jet-range-consumer.RbIhbg/tappath-kernel.log`; assumption printing of
the public result passes with exit 0 (session 62680).

Assumption printing session 62680 completes with exit 0, retaining the six
existing recorded assumptions for the public tappath theorem. The kernel
check remains live; no new coverage or acceptance is claimed.

## Empty-buffer writer layout continuation

While tappath kernel checking continues, the separate empty-buffer writer
layout target is repaired without changing its dependencies. Correct the
frame tuple and derive indexed cell separation and positive-capacity head
separation from its original writable-frame contract. This retains all
writeBit/skipBits calls, arbitrary padding contents, cursor/prefix/framing
conclusions and theorem statements. Whole target compilation completes with
exit 0 (session 32061), including the run/cells/call dependencies.

`buffer-empty-layout-repair.patch` SHA-256:
`e22047f15869639ea1ca69e3444b8a70cf585dddce0ff4ea9ff878be1d29e0aa`.
All definitions/statements compare unchanged and reverse applicability passes.
Independent whole-chain kernel checking passes with exit 0 (session 57423), log
`/tmp/jet-range-consumer.RbIhbg/buffer-empty-layout-kernel.log`.
Tappath and empty-buffer kernel handles are now terminal. Assumption printing
of both empty-buffer results passes (session 67572), using six inherited
assumptions. No new axiom or statement change is introduced.

## Initialized SHA context-writer layout continuation

The final identified SHA frame-tuple consumer is repaired in
`jet_write_sha256_context_empty_layout.v`: derive head separation from 830-bit
capacity and indexed separation for its first 510 encoded buffer cells.
The actual buffer, counter and IV writer calls, arbitrary padding, final
canonical output, cursor and outside-memory conclusions are unchanged.
All definitions/statements compare unchanged and reverse applicability passes.

`sha-empty-context-repair.patch` SHA-256:
`3843bfaf2ad6153de6c55859adc93855580eaa36f2c7d49aaed0904eb9c9f1f5`.
Whole-module compilation passes with exit 0 (session 1972).
Independent whole-chain kernel checking passes with exit 0 (session 24754), log
`/tmp/jet-range-consumer.RbIhbg/sha-empty-context-kernel.log`.
The accepted source fingerprint and registered coverage remain unchanged.

The subsequent whole build is session **58406**, started after the context
target finished compiling. It does not recompile that module or its unchanged,
already-built dependencies, so the independent kernel input remains stable.
Poll the build and kernel handles before further dependent edits.
Context-writer assumption printing passes with exit 0 (session 60845), using
the six inherited assumptions; complete candidate snapshot review remains open.

## Present-buffer segment continuation

Build session 58406 is terminal with exit 2 at `jet_present_buffer_segment.v:71`.
The obsolete tuple labels writable metadata permission `HD` and passes it as
indexed word separation. While its remaining Bitcoin raw-jet worker was live
at 98.8% CPU, the repair was first checked in a separate complete scratch
module `present_buffer_probe.v`, without editing any worker input. After that
build became terminal, apply the identical checked source to the actual module.
Whole-module compilation passes with exit 0 (session 44177). Both definitions
and theorem statements are unchanged; the module and probe match byte-for-byte.
The repair derives the tag's indexed separation and prefix head separation
from initial capacity, retaining the actual tag/byte-array execution and
writable continuation; no extra output or execution premise is added.

`present-buffer-repair.patch` SHA-256:
`d8c0c42249148badf8861d84568ec6acbf66fd39079db65f5f1c3ea9c791e65c`.
Reverse applicability passes. Independent whole-chain kernel checking passes
with exit 0 (session 6451), log `/tmp/jet-range-consumer.RbIhbg/present-buffer-kernel.log`.
Assumption printing passes with exit 0 (session 41919), retaining the six
inherited assumptions. Subsequent whole-build session **69499** is now running
after the target compiled, without changes to the kernel check's dependencies.
Poll it and kernel session 6451. Accepted input hash and coverage remain unchanged.

## Mixed-buffer writer loop continuation

Whole-build session 69499 is terminal with exit 2 at
`jet_write_buffer8_loop_layout.v:88`, where writable metadata permission is
misused as indexed cell separation. Correct the frame tuple and retain its
capacity function. Derive indexed separation using `byte_chunk_cells_width`
and derive head separation from the positive initial capacity. The inductive
tag decisions, byte/padding calls, actual loop execution, continuation and all
output/memory observations are retained; definitions/statements compare unchanged.

`buffer-loop-repair.patch` SHA-256:
`ddf9311eba20625fc85db2703d672da8e129e4e0e0bed15ed391fca08766e1d3`.
Whole-module compilation passes with exit 0 (session 30191), and reverse
applicability passes. Independent whole-chain kernel checking is running as
session 21988, log `/tmp/jet-range-consumer.RbIhbg/buffer-loop-kernel.log`.
Assumption printing is session **52480**. Poll these exact handles.
The present-buffer kernel check is complete, not still running. No additional
jet registration or acceptance is claimed.

Assumption printing completes with exit 0 (session 52480), using the six
inherited assumptions. Subsequent whole-build session **83713** is running
with the checked target/dependencies unchanged; poll it and kernel 21988.

## General SHA context layout continuation

Mixed-buffer kernel session 21988 passes with exit 0. Whole-build session
83713 is terminal with exit 2: general SHA context writing misuses metadata
writable permission as cell separation at line 89, and context reading times
out in byte-array preservation arithmetic at line 119.

The writer derives head and indexed separation from initial 830-bit capacity,
including arbitrary encoded buffer contents. The reader first derives the
index bound from only its actual list-length facts, then solves store/load
separation with only that bound. The original ten-second deadline is unchanged;
the large context/payload facts are not unfolded or fed to arithmetic search.
Both whole modules compile with exit 0 (session 69719). All definitions and
theorem statements compare unchanged; reverse applicability passes.

`sha-context-general-repair.patch` SHA-256:
`4d6d4d8569e334c00145fb96fe9ff7e2c37f7d3d24197f2f26171b7f2c65182d`.
Independent joint whole-chain kernel checking passes with exit 0 (session 40939),
log `/tmp/jet-range-consumer.RbIhbg/sha-context-general-kernel.log`.
Both execution results' assumption printing is session **17319**. Poll these
handles; accepted inputs/coverage and full candidate acceptance are unchanged.

Assumption printing passes with exit 0 (session 17319); both execution results
use only the six inherited assumptions. Subsequent whole-build session **5609**
is running with the checked kernel inputs unchanged. Poll it and kernel 40939.

## Repair archive replay audit

All 26 continuation patches touch 44 distinct, nonoverlapping sources, and all
reverse applicability checks pass against the current isolated tree. A separate
read-only forward replay from the exact candidate commit
`00536113eb285b109f00c28a0fd22de66b05ec35` reproduces all 44 current source files
byte-for-byte. No file or Git object is written by this diagnostic.

The initial strict line-number replay rejects `secp-frame-repair.patch` because
its handwritten hunk header is one line early. Matching its full old context
resolves exactly one location, at offset +1, and gives the exact current source.
This is a valid patch offset, not a source mismatch; the patch/hash are retained.
All other hunks match their declared original positions exactly.

The general SHA context kernel session 40939 is complete, giving 43 repaired
whole modules with independent kernel receipts. The remaining value/hash module
has only its sequencing lemma checked in isolation until the live broader build
reaches it. Whole-build session **5609** remains live and has advanced through
SHA context/tagged-context and Bitcoin tapleaf/tapbranch construction consumers.
No new compiler is started and no accepted coverage is claimed.

Local signing availability was freshly checked: the configured public key
`/Users/brenorb/.ssh/git_signing.pub` cannot obtain a signature from the SSH
agent ("agent refused operation"). No signing setting is disabled or changed,
no commit is claimed and no push is performed. This blocks commits, not further
proof checking; the full goal remains active.

## Whole range-candidate compilation completed

Whole-build session **5609** now terminates with exit 0. It compiles the complete
original range candidate plus all 26 continuation patches, including the SHA
finalize bridge and `jet_bitcoin_vh_hash_prep.v`. This establishes whole-module
compilation for the previously lemma-only value/hash repair. Independent
whole-chain kernel checking of that module is running as session **77668**;
its log is `/tmp/jet-range-consumer.RbIhbg/vh-prep-kernel.log`.

This is not acceptance or coverage growth. The scratch candidate predates the
accepted odd/zero extension. Next reconcile all 18 exact accepted predicate
sources and compile their public contracts against the range correction, then
review definitions/types/assumptions and perform independent full acceptance.
The accepted-tree input fingerprint remains
`6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`.

Assumption printing for all three value/hash declarations completes with exit 0
(session **59802**). `write_cells_seq` retains the four inherited classical/
extensionality assumptions; `repr_signed_word` and `vh_regs_eq` are closed under
the global context. Kernel session 77668 is still live; poll this exact handle.

## Reproducible continuation replay checker

`check-continuation.py` now reproduces the journal-hash, reverse-applicability
and byte-exact forward replay checks without writing files or Git objects.
It passes on `/tmp/jet-range-consumer.RbIhbg`: 26 patches and 44 sources.
Two in-memory negative fixtures reject both a changed patch byte and a changed
repaired-source byte. This checker does not replace original-series replay,
proof compilation, kernel checking, definition/assumption review or acceptance.
No input to the live kernel checker was changed.

## Accepted predicate-extension reconciliation

All 18 predicate sources from `cafb9b31` are materialized byte-for-byte in
`/tmp/jet-range-predicates.ryJp78`, separate from the frozen range-candidate
inputs. Compilation against the rebuilt range dependencies passes with exit 0
(session **60425**). Both `fe_odd_local_spec` and `fe_zero_local_spec` are included;
all 18 compiled modules are newer than their exact source files. No source,
canonical program, public conclusion or execution premise is changed.

The initial sequential attempt (session 63866, exit 1) used project-list order,
which is not dependency order: `jet_secp_field_predicates` requires the later
listed `jet_secp_canonical_odd`. Reading actual imports supplies the topological
order for the successful run. This was a missing compiled dependency, not a
failed proof. The overlay is mapped as `C` alongside the existing range tree.

Public assumption printing passes with exit 0 (session **78744**): both public
contracts retain the same six inherited assumptions, without a new libc,
execution or output premise. Value/hash kernel
session **77668** remains live and its inputs are unchanged. Whole-chain kernel
checking of the predicate overlay and full reconciled acceptance are still
required; successful compilation alone does not accept the range correction.

## Reconciled predicate kernel check and contract comparison

Predicate overlay whole-chain kernel checking passes with exit 0 (session
**55604**), log `/tmp/jet-range-predicates.ryJp78/kernel.log`. Its context summary
has the existing 15 library assumptions and reports no type-in-type, unsafe
fixpoints or assumed positivity. The value/hash check 77668 remains live.

A separate complete snapshot-printing source in the overlay compiles with
exit 0 (session **20400**), producing `contracts.out` and empty `contracts.err`.
It prints the accepted 3,577 results, all six range support additions, and the
current 1,823 frozen definitions against the reconciled dependency graph.
Read-only comparison finds 3,559 existing theorem types unchanged and 18
changed support types. Seventeen preserve their exact outer conclusion modulo
printing whitespace: their changes concern metadata-range/indexed separation.
The remaining `wh_bounds` result removes its obsolete block-inequality
conclusion and retains numerical bounds; the real wide-copy execution
conclusions are unchanged. This internal helper is not a jet contract.

The complete printed diff has 20 context hunks: the above support-type changes,
six appended support results, and the `write_frame_at` definition replacing
blanket block separation with separation at each writable word. No canonical
definition changes appear. Review of each changed premise's domain and the
full reconciled assumption audit remains required before snapshot acceptance.
These comparison diagnostics do not update any accepted snapshot.

## Full reconciled assumptions and old-domain inclusion

Full assumption printing for the same 3,583-result reconciled inventory is
running as session **84751**, with output/error logs
`/tmp/jet-range-predicates.ryJp78/assumptions.out` and `assumptions.err`.
On completion compare every prior per-result set against the accepted snapshot;
review the six new support sets separately. Printing a prefix is not acceptance.

`range-domain-review.v.source` preserves a complete formal lemma
`accepted_write_frame_at_included`. Its legacy predicate is the exact accepted
`write_frame_at` definition with only the identifier renamed. The proof derives
the candidate's indexed separation by the old distinct-block alternative and
preserves every other field, permission, address, count and initial-load fact.
This establishes inclusion of all old inputs, not adequacy of every new domain
or a new jet equivalence. Complete compilation passes with exit 0 (session
**7081**) and retains four inherited classical/extensionality assumptions.
Independent whole-chain kernel checking passes with exit 0 (session **84983**),
log `/tmp/jet-range-predicates.ryJp78/domain-kernel.log`.

Archived source SHA-256:
`c02d101f00e5ac84892a1b0b83f32b0d7645b3267ebc0975fa23a7472a338616`.
This supporting source is outside the accepted build and original range
manifest, and is not covered by the continuation-patch replay checker.
Value/hash kernel session **77668** remains live; no checked input changed.

## Concrete witness through the repaired candidate's writer

`range-embedded-review.v.source` reuses the archived 24-byte allocation witness,
now invoking the actual candidate `C.jet_writeBit_layout_total` theorem instead
of the historical separate diagnostic writer. Its complete theorem constructs
metadata and backing data by allocation and actual stores, admits all 64 initial
cells under the candidate frame predicate, and proves old-predicate rejection.
For an arbitrary initial int64 word and either Boolean input, it concludes the
real C call, output bit 63, prefix preservation, cursor 63, outside-range loads,
permission preservation and valid-block preservation. This is shared-writer
domain evidence, not an additional registered jet or a claim of full evaluator
admissibility. It does not claim the diagnostic's separate 63-cell continuation
result; the exact candidate writer contract is used.

Whole-module compilation passes with exit 0 (session **85290**), retaining only
the six inherited assumptions. Independent whole-chain kernel checking is live
as session **1961**, log `/tmp/jet-range-predicates.ryJp78/embedded-kernel.log`.
Source SHA-256:
`7eb29cea32f27384f4b37d6d15a07b4a780497fa55a795d56f7b05b36f1d9ab6`.
The source is outside accepted build paths and both original manifests; its
hash is recorded here, not added to the continuation-patch replay scope.
Full assumption session **84751** and value/hash kernel **77668** remain live.

Embedded witness kernel session **1961** completes with exit 0, retaining the
existing library context and reporting no type-in-type, unsafe fixpoints or
assumed positivity. `RANGE-CONTRACT-REVIEW.md` records the scoped semantic and
interface review, formal old-domain inclusion, concrete candidate-writer
witness and remaining acceptance/domain obligations. It is not an acceptance
receipt. The full assumption and value/hash checks remain live.

## Final repaired-module kernel result

Value/hash kernel session **77668** now passes with exit 0; the log ends with
all three declarations of `C.jet_bitcoin_vh_hash_prep` successfully checked.
This completes independent whole-chain kernel receipts for all **44** repaired
modules. The full original candidate build, the 18-source predicate overlay,
the old-domain inclusion and concrete candidate-writer witness also compile
and pass their recorded kernel checks. These are not full acceptance.

Full reconciled assumption session **84751** remains live and has advanced
through word-extension/rotation bridges. Poll that exact handle; do not infer
whole-inventory equality from the already matching prefix.

## Integration-input checks while the assumption audit runs

The candidate's original-source gate passes against the current repository via
`JET_C_REPO`: all 240 production/canonical/configuration inputs match. Its
proof-integrity scan also completes separately; neither substitutes for AST
regeneration or final acceptance. The older candidate lacks precisely the 18
tracked predicate proof sources already verified in the overlay. Its project
lists and scripts also predate their registrations/source gates. Preserve the
current accepted checker/registry/project additions when assembling the final
candidate, rather than copying the old metadata wholesale. In particular keep
the predicate checker and its negative tests in the final full audit.

## Concrete complete one_8 call on shared storage

`range-one8-review.v.source` extends the concrete allocation review to an
actual arithmetic jet, invoking the candidate's complete
`eval_one8_layout_matches_spec`. For arbitrary int64 initial data and environment
value it constructs one 24-byte allocation, admits eight writable output cells,
derives the real source-frame byte copy from metadata loads, and proves the C
call of `f_simplicity_one_8`, canonical `one8_spec` output, prefix, cursor 56 and
the complete outside-memory conclusion. Source/destination metadata alias at
offset zero and output data occupies [16,24); the old frame predicate rejects
this initial memory. This is a concrete domain witness at cursor 64, not a
replacement for the existing arbitrary-cursor jet theorem or new coverage.

Whole compilation passes with exit 0 (session **18892**), retaining the six
inherited assumptions. Independent whole-chain kernel checking passes with
exit 0 (session **13355**), log
`/tmp/jet-range-predicates.ryJp78/one8-kernel.log`, without unsafe kernel flags.
Source SHA-256:
`9944097943fc0d27e1dbd8e1bae8b0ac1cd0eade1f77fce404ca6ab03b6506e4`.
This source remains outside accepted builds/original manifests/repair-patch
replay scope, alongside the other complete review witnesses.

Literal-source inspection confirms catalog `One8 = Prog.one word8` and
`Programs.Arith.one w = true >>> left_pad_low word1 w`; `jet_spec.v` uses that
composition and the three word1-to-word8 recursive padding layers. No C or
canonical program is modified. Full assumption session **84751** remains live.

## Fresh original-source AST verification

All four original-source regeneration/comparison checks pass together with
exit 0 (session **30097**), using CompCert 3.14 and the pinned glibc-2.36 sysroot.
The current repository's regenerated core, Bitcoin, SHA and secp ASTs match
their committed artifacts. A subsequent byte comparison confirms those four
artifacts also equal the isolated range candidate's AST inputs. This uses the
unchanged configuration already checked by the 240-input source-target gate.

Retained generated copies:

- core: `/var/folders/yb/vzwjjpzs7mn47ftjxrl929rh0000gn/T/simplicity-jets-check.jxgycX/jets.v`
- Bitcoin: `/var/folders/yb/vzwjjpzs7mn47ftjxrl929rh0000gn/T/simplicity-bitcoin-jets-check.6C1ViO/jets_bitcoin.v`
- SHA: `/var/folders/yb/vzwjjpzs7mn47ftjxrl929rh0000gn/T/simplicity-sha-jets-check.x6ivK3/jets_sha.v`
- secp: `/var/folders/yb/vzwjjpzs7mn47ftjxrl929rh0000gn/T/simplicity-secp-jets-check.49kunc/jets_secp.v`

No AST, C source, canonical program, proof source or accepted snapshot changes.
Accepted input fingerprint remains
`6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`.
This independent source/AST evidence supplements, not replaces, the required
full reconciled acceptance run. Full assumption session **84751** remains live.

## Full reconciled assumption audit completed

Session **84751** terminates with exit 0 and an empty error log. Read-only
comparison of the entire output confirms all **3,577 accepted assumption
records unchanged**, no missing/duplicate result, and exactly six new range
support results. Each new result uses the four existing classical/extensionality
assumptions, with no new axiom name or external-call/execution/output premise.
The complete reconciled inventory is **3,583 results, 1,860 closed**.

The six additions are `write_frame_at_head_separate`,
`write_frame_at_crossing_separate`, `word_store_preserves_frame_load`,
`frame_store_preserves_word_load`, `write_frame_at_slice_crossing_separate`,
and `noop_long_store_preserves_long_load`, under their recorded modules.
No verification process from this continuation remains live. The next step is
assembly of the exact reconciled candidate, reviewed snapshot comparison and
independent full acceptance. Accepted inputs and coverage remain unchanged.

## Reconciled candidate assembled and independent acceptance launched

The isolated `/tmp/jet-range-consumer.RbIhbg` now includes all 18 exact accepted
predicate sources, current project lists, predicate source/negative gates,
coverage metadata/checker, and current frozen-definition inventory. Its public
inventory preserves all 3,577 accepted entries in order and appends the six
range support entries. Candidate snapshots come from the complete reviewed
printer and assumption output, not from an unreviewed update run. The kernel
axiom allowlist remains byte-identical to the accepted version.

Both original C and Haskell input directories are linked to the unchanged
current source target so original generation scripts run in the isolated root.
No source in those directories is modified. Candidate whole compilation passes
with exit 0 (session **88015**), freshly rebuilding all 18 predicate modules in
the same physical tree as their range dependencies. Registry remains 349/533.
Frozen candidate input SHA-256:
`dccfcbcd42e6b7c419992597362ebf4a2c2df407769183a217a27599718e8f07`.

Independent `check-jets.sh --accept` is running as session **54683**, log
`/tmp/jet-range-consumer.RbIhbg/reconciled-accept.log`. It uses no update or
no-build flags, Coq 8.17.1, two build jobs, the existing 65,520 KiB checker stack,
CompCert 3.14 and the pinned glibc-2.36 sysroot. Poll this exact session and keep
all its source/metadata/snapshot inputs frozen. Starting the run is not
acceptance. Accepted checkout input hash remains
`6868621c6ba1d84ad9995f163cf83d3a863dff18004ba608cb3070607469a093`.

## Guarded integration manifest

`RECONCILIATION.json` records the guarded integration inputs against accepted
base `cafb9b31`: all 870 tracked Coq fingerprint inputs are present, with no
unexpected candidate inputs. Exactly 149 differ: 146 proof sources and three
inventory/snapshot files. Each records accepted and candidate SHA-256, and all
prospective targets currently equal their accepted Git content (no overlapping
user edits). This excludes unrelated untracked checkout inputs; it neither
removes them nor adds them to the candidate. Guard these hashes again before
integration after acceptance. The manifest is not an acceptance certificate.
