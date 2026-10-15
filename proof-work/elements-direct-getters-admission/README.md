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

## Acceptance boundary and continuation

Preparation and independent review passed. All selected source checks and
their 32 mutations, twenty evidence mutations, coverage tests and the ordinary
full contract comparison passed; `REVIEW.json` seals this evidence. Full
acceptance and installation are not yet claimed.
Main remains at **368/533**, with 104 explicit `memcpy_model` conditions.
The candidate inventory is **371/533**, not accepted coverage until the full
normal gate terminates successfully. The all-jet goal remains unfinished.
These receipts describe the actual dirty/staged checkout, including the
preexisting shared word-conversion module, not a clean-HEAD build.

Do not alter main Coq/C/Haskell sources while its predecessor sequence audit
is live (session 42404, log in the sequence candidate). Poll the real handle;
a recorded identifier alone is not liveness. Its successful actual-main
receipt is a prerequisite for any subsequent main installation.

```sh
ulimit -s 65520
python3 -B proof-work/elements-direct-getters-admission/review.py finish /private/tmp/jet-direct-getters-admission.yc45qogt
python3 -B proof-work/elements-direct-getters-admission/accept.py /private/tmp/jet-direct-getters-admission.yc45qogt
```

Do not duplicate live checks. `accept.py` runs exactly
`bash check-jets.sh --accept`, without update/skip flags. It pins the reviewed
tools, evidence and input fingerprint, preserves terminal status/log hashes,
and requires every build, kernel, assumptions, contracts, negative-test and
five-AST check. `AUDIT-RUN.json` records launch, not success;
only `ACCEPTANCE.json` records a successful terminal full audit.
No main installation or compiler-object copying is performed by these tools.

Full isolated acceptance was launched as session **54262**, with log
`/private/tmp/jet-direct-getters-admission.yc45qogt/acceptance.log`.
Poll this handle rather than duplicating the run. Main's sequence audit
session **42404** also remains live; its 978-module recursive check passed.
The preparation commit is `6f1fb64d`, pushed only to `brenorb/simplicity`.

The guarded continuation tools are prepared but have **not** installed main:

```sh
python3 -B proof-work/elements-direct-getters-admission/install.py /private/tmp/jet-direct-getters-admission.yc45qogt
python3 -B proof-work/elements-direct-getters-admission/post-check.py
ulimit -s 65520
python3 -B proof-work/elements-direct-getters-admission/main-accept.py
```

The one-time installer requires this candidate's successful terminal full
acceptance **and** the predecessor's successful actual-main sequence receipt
and postcheck. It binds both histories, copies only the exact reviewed source/
metadata/guard delta (no `.vo`), checks full input identity and preserves the
original staged patch. Do not run it until both audits are terminal and green.
The new postcheck then replaces the historical sequence postcheck for current
source identity; predecessor postchecks intentionally do not match later trees.
