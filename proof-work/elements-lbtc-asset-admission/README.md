# Original C lbtc_asset: normal-registration candidate

Proposed successor: **402/533**, adding only `simplicity_lbtc_asset` to the
reviewed 401-jet predecessor. Main is now **401/533**. This candidate is not
installed and does not yet have full normal acceptance.

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

## Guarded successor installation is prepared, not executed

Exactly sixteen source-only targets are permitted: seven metadata/snapshot
files, four gate/printer scripts, two source guards and three new proof modules.
No inherited proof source overwrite is allowed. The installer requires real
actual-main401 and isolated402 success with matching logs, drivers, reviewed
evidence and source identity. Its postcheck validates historical predecessor
receipts without running the obsolete exact-main401 postcheck on main402.
Original staging and unrelated source are preserved. Do not install until both
live audit handles have successfully terminated; then run the installer once,
its composed postcheck, and distinct actual-main402 acceptance.

The newer combined407 plan supersedes that serial next step. This reviewed
delta is included unchanged in407, alongside the404/406/407 deltas. Its full
audit runs against all407 entries, and guarded installation will use the real
accepted401 baseline plus actual-main401 success. Do not install402 or launch
actual-main402 while following the combined plan. Let the existing isolated402
audit finish and preserve its result. The tested402 installer remains a
historical alternative, not an instruction to bypass the combined plan. See
`../elements-output-nonce-admission/README.md`.
