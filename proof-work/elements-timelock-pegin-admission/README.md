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

## Remaining acceptance and installation

The proposed registry is **378/533**, including the unchanged 104 explicit
`memcpy_model` conditions. It is not accepted coverage yet. Main remains at
371/533, with the distinct actual-main getter audit (session 74479) still
running when this preparation was written. Its inputs remain frozen.

```sh
python3 -B proof-work/elements-timelock-pegin-admission/review.py review /private/tmp/jet-timelock-pegin-admission.dw295nit
```

Full isolated acceptance has now been launched **once**, as session **96260**,
with input fingerprint
`545af5c820533dfebce815c8d03aeb3db3aef9235b6e4bad03a73e32f8df78de`.
The exact driver is `accept.py`; its log is
`/private/tmp/jet-timelock-pegin-admission.dw295nit/acceptance.log`.
It runs the normal
`bash check-jets.sh --accept` without update/skip flags. `AUDIT-RUN.json` is a
launch record, not success. Only terminal `ACCEPTANCE.json`, its unchanged
source fingerprint and the complete final log marker establish acceptance.
The launcher refuses to overwrite an existing launch. Poll the existing
handle; silence or an observation timeout is not a failed run.

Installation requires both the candidate's terminal acceptance and the
371-jet actual-main audit's successful terminal receipt/postcheck. Reuse the
guarded source-only installation pattern from the direct-getter batch: exact
metadata/script/guard/four-source delta, archived patch and ledger, no copied
objects, unchanged original staging, then a distinct actual-main acceptance.
Do not rerun completed predecessor installers or their historical postchecks
against a later source state. These receipts describe the actual dirty/staged
checkout, including preexisting untracked dependencies, not clean-HEAD
reproducibility.

The original frame/cursor/prefix/environment/memory contracts and
LP64/RECKLESS configuration are unchanged. Environment-builder/evaluator
composition, assertion-enabled builds, remaining conditional-library
obligations and all other missing jets remain in the full objective. No
admission or unchecked cast is used; this batch does not complete that goal.
