# Eight indexed/current digest getters: reviewed normal candidate

Scope: the input/current script-hash and scriptSig-hash getters, and the
indexed/current issuance asset-proof and token-proof hash getters. The eight
coverage entries refer only to their actual-C endpoint contracts, with the
checked literal conversion/view adapters and mandatory source gates. Other
jets in their existing C dependency modules are not added to coverage.

Candidate: `/private/tmp/jet-digest-getters-admission.jd1i0nr6`.
The baseline is the fingerprint-bound seven-jet timelock/pegin candidate at
`545af5c8...`. At assembly its audit was still running; it has now passed and
been installed through its own guarded receipt/ledger, not through this batch.
Objects were copied only from the completed immutable final-name pegin proof
tree. The predecessor supplies source-text deltas only. Before any additions,
the reconstructed baseline fingerprint was verified byte-identical to the
reviewed predecessor's. No outputs were copied from a running audit.

## Preparation and independent review passed

The whole normal build and fresh compilation of both new modules passed.
The delta contains nineteen results and eleven definitions, all with complete,
untruncated deep prints. All **8,162** inherited contract records retain their
exact bytes/order, and all **5,377** inherited assumption sets are unchanged.
Every new result has its separately checked dependency set; all eight final
contracts retain their originals' six inherited assumptions. The shared
conversion and two proof-view lemmas remain closed. No new model premise,
axiom or unchecked cast is introduced.

Only the two new modules gain explicit-parameter printing. Their names are
loaded without opening them, preserving inherited resolution. Coverage accepts
only the exact functions, linked/logical environments, indexed/current widths
and whole separated contracts. Fifty-six new coverage rejection fixtures
passed. Each mutation is confined to the selected theorem statement rather
than accidentally changing a later definition.

The ordinary full contract comparison, both source guards, their **68** source
mutations (30 script-hash and 38 issuance), and **26** admission/evidence
corruptions passed. `ASSEMBLY.json`, `PREPARATION.json` and `REVIEW.json` bind
the source maps, checked proof bases, virtual predecessor, original staging,
inventories, commands, successful exits, objects and complete reports. The
review binds eight successful stages and 1,244 report/object evidence hashes.
Full added reports and all eight review-stage logs are archived here.

The resulting input fingerprint is
`f362c5187bf3554d8703f739275629c64a154f4e9098e3185e2a9e9e49e7dec8`.
The proposed count is **386/533**, including the unchanged 104 explicit
`memcpy_model` conditions. This is not yet accepted coverage.

```sh
python3 -B proof-work/elements-digest-getters-admission/review.py review /private/tmp/jet-digest-getters-admission.jd1i0nr6
```

## Full isolated acceptance passed

Main's distinct 371-jet acceptance and the seven-jet predecessor's isolated
full audit both passed with exit 0. The predecessor is now installed at
378/533, with source/index/history identity verified by its composed postcheck.
Its separate actual-main audit **3224** has now passed with exit 0 and exact
source/index validation. Sessions 3224 and 96260 are terminal: do not poll or
restart them.

`accept.py` refuses to launch until the seven-jet candidate has a successful
terminal acceptance, guarded source-only installation and passing composed
postcheck at exactly `545af5c8...`. It also requires this candidate's terminal
review/evidence hashes and refuses to overwrite an existing audit launch.
Its missing-predecessor guard was tested without launching an audit or
changing main/index. After the required receipts and installation existed,
it was launched **once**, as session **87596**, with fingerprint
`f362c518...`. It completed with exit 0 after **3,722.56 seconds**. Build,
all 1,025 kernel modules, the assumption/contract audits, negative suites and
all five AST regenerations passed. `ACCEPTANCE.json`, `TERMINAL.json` and the
complete durable `acceptance.log` (SHA-256 `ecfcdc4c...`) bind that outcome.
`AUDIT-RUN.json` remains a historical launch, not a success receipt.
Log: `/private/tmp/jet-digest-getters-admission.jd1i0nr6/acceptance.log`.
The launch command was:

```sh
ulimit -s 65520
python3 -B proof-work/elements-digest-getters-admission/accept.py /private/tmp/jet-digest-getters-admission.jd1i0nr6
```

It runs exactly `bash check-jets.sh --accept`, without update/skip flags.
This run is terminal: preserve its receipt/log and do not repeat the command
above. The predecessor's distinct actual-main audit also passed; **both**
prerequisites now permit guarded installation of these eight getters. Never copy compiler objects
to main or silently commit unrelated staged metadata. Retain an exact owned
installation patch/ledger, verify main equals this accepted candidate, then
run a distinct actual-main acceptance. The composed review permits main only
at one of the exact known predecessor checkpoints, not arbitrary edits.

Original separated frames, arbitrary output contents, cursor/prefix, logical
environment representation and memory-change contracts remain unchanged,
as does the LP64/RECKLESS scope. The digest getters copy represented cached
values; this does not prove caller construction of those caches. The source
guards review selected canonical ports, not formal equivalence of host lens
or cryptography implementations. These receipts describe the actual dirty/
staged source base, not clean-HEAD reproducibility. All other jets, caller/
environment obligations, conditional library links and remaining fidelity/
configuration work stay in the unfinished all-jet goal.

## Guarded integration lifecycle prepared, not executed

`install.py`, `post-check.py`, and `main-accept.py` are prepared for use only
after sessions 3224 and 87596 both terminate successfully. Three early refusal
guards passed: repeated installation, missing isolated acceptance, and missing
actual-main predecessor acceptance. The tests prohibit subprocesses/writes
inside those early-guard experiments and verify unchanged main inputs/index.
`LIFECYCLE-REVIEW.json` records that **positive installation is not yet tested**.
No integration or actual-main 386 acceptance is claimed by these scripts' presence.

The installer compares against the reconstructed **378 baseline**, not the
older 371 checkout that existed when the candidate was first assembled. It
requires both real terminal receipts and their log/input/review/driver hashes,
then copies only seven metadata/snapshot files, four scripts, four new guards,
and two new proof sources. It preserves the entire original index, records the
exact owned delta/ledger, and requires installed main to match the accepted
386 source fingerprint. No compiler objects are copied. The postcheck composes
the historical predecessor acceptance, isolated acceptance and current source
identity; the separate main audit refuses duplicate launches.

Once both prerequisites pass, archive their complete logs/terminal receipts
before invoking this **one-time** installation, then its postcheck and distinct
actual-main audit. Do not execute these commands merely because kernel checking
has passed; all remaining acceptance stages must also pass.

```sh
python3 -B proof-work/elements-digest-getters-admission/test-lifecycle.py
# Only after both complete terminal acceptances:
python3 -B proof-work/elements-digest-getters-admission/install.py /private/tmp/jet-digest-getters-admission.jd1i0nr6
python3 -B proof-work/elements-digest-getters-admission/post-check.py
ulimit -s 65520
python3 -B proof-work/elements-digest-getters-admission/main-accept.py
```
