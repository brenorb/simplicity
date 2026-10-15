# Seven Elements jets: normal admission candidate

The isolated candidate adds the checked whole-C contracts for:

- `simplicity_tx_is_final`
- `simplicity_tx_lock_height` and `simplicity_tx_lock_time`
- `simplicity_check_lock_height` and `simplicity_check_lock_time`
- `simplicity_input_pegin` and `simplicity_current_pegin`

Candidate: `/private/tmp/jet-timelock-pegin-admission.dw295nit`.
The immutable proof base is the final-name pegin tree, containing the five
final-name timelock/assertion proofs as well. Every inherited main source
matches that base byte-for-byte. No compiler outputs are copied from main's
live audit. Four new proof sources, eight mandatory source/negative guards,
and the exact seven coverage entries are proposed. Other jets in the shared
dependency modules are not added to coverage.

## Verified preparation

The whole normal build passed, followed by fresh compilation of all 34 added
modules in dependency order. Complete reports cover 308 result types and 208
definitions, including identifiers ending in apostrophes. All 7,646 inherited
contract records retain their exact bytes and order; all 5,069 inherited
assumption sets are unchanged. New assumption sets match the checked
prerequisites exactly, with no new axiom. The three pure timelock bridges are
closed. The pegin semantic bridges retain functional extensionality and
CompCert contracts retain their original inherited dependencies; they are not
misclassified as closed. No new library model premise is added.

All 516 new records have complete deep prints. The 24 compact prints containing
elision have matching full supplements, not ignored gaps. Only newly registered
modules gain explicit-parameter printing; the shared partial-contract transport
is loaded without opening it to preserve inherited names.

Coverage accepts only the exact function, linked/logical environment and
input/output contract shapes. Forty-nine new fixtures test wrong functions,
environments, both widths, contract kind and extra premises. Mutations are
restricted to each theorem statement: otherwise a multiline type can make a
literal text replacement alter a later definition instead. These deliberately
corrupted fixtures are never compiled.

The source guards retain the recursive finality program, lock threshold and
arithmetic port, assertions/failure returns, both pegin presence tags and exact
index/digest conversions. They also pin the entire environment/whole-call
contracts, not just a named output expression. Their mutation suites contain
108 source corruptions (31 finality, 32 lock, 25 check-lock, 20 pegin).

`ASSEMBLY.json`, `PREPARATION.json`, full added contract/assumption logs and the
independent `review.py` bind inventory, source/object identities, exact compiler
commands, successful exits and preservation of main and its original index.
`review.py finish` additionally checks ordinary full contract comparison,
coverage fixtures, all four source/negative pairs and evidence-corruption
tests. Only its terminal `REVIEW.json` permits full acceptance to start.

The independent review has now **passed**, including the ordinary whole
contract comparison, all coverage fixtures, all 108 source corruptions and
26 in-memory evidence corruptions. `REVIEW.json` binds 12 successful check
commands, 24 checked deep supplements and 1,278 report/object evidence hashes.
The full added reports and all twelve review-stage logs are archived here.

## Full isolated acceptance and source-only installation passed

The isolated registry at **378/533** passed full normal acceptance, including
the unchanged 104 explicit `memcpy_model` conditions. Session **96260**
terminated with exit 0 after **3,397.39 seconds**. All 1,023 kernel-checked
modules, assumption audit (5,377 results, 2,965 closed), full contracts,
negative suites and all five production AST regenerations passed.
`ACCEPTANCE.json`, `TERMINAL.json` and the complete durable `acceptance.log`
(SHA-256 `eac815da...`) bind the unchanged `545af5c8...` input fingerprint.
The predecessor's distinct actual-main 371-jet audit also passed.

```sh
python3 -B proof-work/elements-timelock-pegin-admission/review.py review /private/tmp/jet-timelock-pegin-admission.dw295nit
```

The completed isolated run used input fingerprint
`545af5c820533dfebce815c8d03aeb3db3aef9235b6e4bad03a73e32f8df78de`.
The exact driver was `accept.py`, running `bash check-jets.sh --accept` without
update/skip flags. `AUDIT-RUN.json` is retained as a historical launch, not a
success receipt. Do not restart or poll that completed run.

The guarded one-time `install.py` verified both terminal histories and
installed exactly seven metadata/snapshot files, four gate/printer scripts,
eight source/negative guards and four proof sources. `INSTALLATION.json` and
`DELTA.patch` bind that exact owned source-only delta. No objects were copied.
Main is byte-identical to the accepted `545af5c8...` candidate at **378/533**;
the entire preexisting index and all other main source bytes are preserved.
The composed `post-check.py` passed with actual-main acceptance still pending.
Do not rerun completed predecessor installers or their historical postchecks
against a later source state. These receipts describe the actual dirty/staged
checkout, including preexisting untracked dependencies, not clean-HEAD
reproducibility.

## Distinct actual-main acceptance passed

Session **3224** completed with exit 0 after **3,685.71 seconds**, with the same
`545af5c8...` fingerprint. Build, all 1,023 kernel modules, assumption/contracts,
negative suites and all five ASTs passed. `MAIN-ACCEPTANCE.json` and
`MAIN-TERMINAL.json` bind that successful outcome and the complete durable
`main-acceptance.log` (SHA-256 `8e59b12d...`). The composed postcheck confirmed
actual-main acceptance, exact source identity and the original index. The old
launch/installation records retain their historical pending flags.

This run is terminal: do not poll or restart it. Until the next installation,
the installed source/index/history can be checked with:

```sh
python3 -B proof-work/elements-timelock-pegin-admission/post-check.py
```

The next eight-getter candidate's isolated full audit also completed with
exit 0 as **87596**. Both installation prerequisites are now satisfied. Use
its guarded installer and postcheck, not a repeated predecessor installer.
After it changes main to 386, this 378 postcheck becomes historical; use the
successor's composed postcheck. The full receipts/logs remain evidence for
this exact 378 source state, not for later changes.

The original frame/cursor/prefix/environment/memory contracts and
LP64/RECKLESS configuration are unchanged. Environment-builder/evaluator
composition, assertion-enabled builds, remaining conditional-library
obligations and all other missing jets remain in the full objective. No
admission or unchecked cast is used; this batch does not complete that goal.
