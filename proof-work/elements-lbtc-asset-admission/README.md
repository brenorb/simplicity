# Original C lbtc_asset: normal-registration candidate

Proposed successor: **402/533**, adding only `simplicity_lbtc_asset` to the
reviewed 401-jet predecessor. Main remains **399/533**. This candidate is not
installed and does not yet have full normal acceptance.

Candidate: `/private/tmp/jet-lbtc-asset-admission.yddis97l`.
Its compiler objects were copied exclusively from the completed private
`../elements-lbtc-asset/` proof tree, not a running audit. The 401 predecessor
supplied fingerprint-bound source only. Neither main nor the original staging
is changed by assembly, preparation, review, or tests.

The original-C whole-call proof, its full statement and canonical Haskell
scribe/endian correspondence are documented in `../elements-lbtc-asset/`.
There is no helper-execution, cached-value, initialized-global or desired-output
premise. Four pure bridges are closed. The C endpoint retains the six inherited
Coq/CompCert assumptions. LP64/RECKLESS and host-library/fidelity boundaries
remain explicit; this is not a formal Haskell compiler or lens-library proof.

Three modules enter the public manifests: the reusable uint32-local initializer,
the concrete lbtc execution support, and the complete literal local contract.
There are two mandatory source/negative gates and one exact whole-function
coverage case, with seven added statement-confined negative fixtures.
No inherited proof source changes, including the predecessor's nullable-128
compatibility repair.

## Preparation and review

Assembly and normal preparation have completed. The normal build and three
explicit fresh compilations pass. `normal-delta-prepare.py` is a shared
preparation engine with explicit batch configuration; both assembly and review
bind its hash. Generating snapshots is never acceptance.

The independent read-only review passes: all **8,339** inherited contract
records retain their bytes/order and all **5,482** inherited dependency sets
are unchanged. The new delta contains **13 theorem types and 12 definitions**.
All 25 have full deep reports; three compact records contain elisions whose
fragments are checked against the retained complete records.
`PREPARATION-CHECKPOINT.json` binds this read-only review to the source,
assembly, preparation receipt and shared engine. The complete new contract and
assumption reports and the build/fresh-compile logs are archived here.

The six-stage finish review **90872 terminated with exit 0**: coverage, coverage tests,
ordinary contract comparison, source correspondence, source corruptions, and
admission/evidence corruptions all pass. The 22 source and 30 admission/evidence
corruptions are rejected. `REVIEW.json` binds the six commands/logs, source
fingerprint, tools, shared engine and 1,252 object/report evidence hashes;
`FINISH-CHECKPOINT.json` independently verifies every recorded evidence hash.
All six stage logs are archived here. Historical launch (completed; do not repeat):

```sh
python3 -B proof-work/elements-lbtc-asset-admission/review.py finish /private/tmp/jet-lbtc-asset-admission.yddis97l
```

`accept.py` is prepared but **has not been launched**. Its preflight requires
real isolated 401 full acceptance and guarded 401 installation with the exact
reviewed source identity and passing postcheck. It may then run alongside the
distinct actual-main 401 audit; any later 402 installation must wait for both
real terminal acceptances. Do not restart either existing audit or copy its
live objects. Main 399 audit **90475** and isolated 401 audit **55506** are still
live. The every-jet goal remains unfinished, including 104 explicit
`memcpy_model` conditional entries and the other missing public jets.

The three negative-only start tests passed without writes or subprocess
launches; `START-GUARD.json` binds the driver, tests and log. Missing real 401
acceptance, missing installation, and duplicate launch are all refused. These
tests do not substitute invented positive receipts for the real prerequisites.
