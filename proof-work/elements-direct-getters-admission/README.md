# Three direct Elements getter contracts: normal admission

Scope: `simplicity_tapleaf_version`, `simplicity_script_cmr`, and
`simplicity_genesis_block_hash`. This batch registers the checked actual-C
contracts together with their literal canonical-source conversion bridges.
The original separated memory, output, cursor and environment contracts are
unchanged. This is not a proof of cached-hash construction or an assumed
execution substituted for C correctness.

Candidate: `/private/tmp/jet-direct-getters-admission.yc45qogt`.
Its immutable proof/dependency base is the separately checked tree documented
in `../elements-direct-getters-normal/README.md`, not the live main outputs.
Three new proof sources and four mandatory source/negative guards are added.
Eight other dependency sources are unchanged. All eleven modules were freshly
compiled after a whole normal build.

## Preparation and independent review

The batch adds 75 public helper/final results and 34 definitions (including the
four-limb numeric word record). All 7,537 inherited contract records remain
byte-identical/in order, and all 4,994 inherited assumption sets are unchanged.
All 27 shared digest-conversion lemmas are closed; the three literal endpoint
contracts have exactly the same assumption sets as their C-execution originals.
No new axiom or unchecked proof shortcut is introduced.

The 109 added records have full deep prints. Nine compact records have checked
deep supplements; they are not ignored. The normal printer gains explicit
parameters only for the eleven newly registered modules, and loads the numeric
helper without opening it so inherited name resolution remains unchanged.
Coverage allows only the three exact separated function/environment/width
contracts; eighteen new negative coverage fixtures reject weakened variants.

`ASSEMBLY.json` and `PREPARATION.json` bind source maps, the original index,
exact inventory deltas, compiler commands, successful exits and object/report
hashes. `new_contracts.log` and `new_assumptions.log` retain the added records.
`review.py finish` additionally runs the ordinary full contract comparison,
coverage tests, both selected source guards and mutation suites, and twenty
in-memory evidence-corruption tests. Invalid proofs are never compiled.
Its terminal `REVIEW.json` is required before full acceptance can start.

## Full isolated acceptance passed; main installation completed

Session **54262** terminated with exit 0 after **3,297.22 seconds**. The command
was exactly `bash check-jets.sh --accept`, without update/skip flags. The normal
build, all 989 kernel-checked modules, assumption audit (5,069 results, 2,800
closed), full contract comparison, negative tests and all five production AST
regenerations passed. `ACCEPTANCE.json` and `TERMINAL.json` bind its terminal
status and unchanged `bf7b39ba...` input fingerprint; the durable complete log
is `acceptance.log` (SHA-256 `6d9e1693...`).

The prerequisite actual-main sequence audit also passed, as recorded in
`../elements-sequence-admission/MAIN-ACCEPTANCE.json`. The one-time installer
verified both histories and installed exactly seven metadata/snapshot files,
four gate/printer scripts, four source/negative guards and three proof sources.
It copied no compiler objects. `INSTALLATION.json` and `DELTA.patch` bind that
exact owned change; all other main source bytes and the original staged patch
remain unchanged. Main's full input fingerprint is byte-identical to the
accepted candidate's. Installed registration is **371/533**, including the
unchanged 104 explicit `memcpy_model` conditions. The all-jet goal is unfinished.

These receipts describe the actual dirty/staged checkout, including the
preexisting shared word-conversion module, not a clean-HEAD build. The exact
registry/snapshot/script worktree delta is retained separately from unrelated
staged changes; it is not silently swept into a commit.

The distinct actual-main getter acceptance **passed**: session **74479**
terminated with exit 0 after **3,298.87 seconds**. `MAIN-ACCEPTANCE.json` and
`MAIN-TERMINAL.json` retain the exact command, terminal status, duration and
unchanged `bf7b39ba...` source fingerprint. The complete durable log is
`main-acceptance.log` (SHA-256 `a82b1986...`). All 989 kernel-checked modules,
the 5,069-result assumption audit (2,800 closed), full contract comparison,
negative suites and all five production AST regenerations passed. The
installed-main postcheck confirms actual-main acceptance, source identity
and preservation of the entire preexisting staged patch.

`MAIN-AUDIT-RUN.json` remains a historical launch record, not the success
receipt. Do not poll/restart this completed run or rerun the one-time installer.
The distinct seven-jet candidate has its own live audit and is not accepted
by this earlier 371-jet result.

```sh
python3 -B proof-work/elements-direct-getters-admission/post-check.py
```

Use this postcheck for the 371-jet source identity: the old sequence
postcheck represents its historical `7e55c862...` source state and intentionally
does not match the later installation. This ledger composes the old source
map, exact new delta and both prerequisite terminal receipts. After a later
reviewed installation changes main's source state, use that installation's
composed postcheck instead of requiring this historical one to match new
inputs. The all-jet goal remains unfinished.
