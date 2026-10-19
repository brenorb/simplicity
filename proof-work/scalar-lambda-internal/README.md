# Scalar lambda: unchanged public contract, fewer inherited dependencies

The nine archived modules compile against the original generated secp program.
The new public C-to-literal-Simplicity theorem and actual-initialization witness
have **six**, rather than the older proof's eight, inherited dependencies.
No implementation, specification, API contract, generation setting or shared
registry is changed. This is an unregistered proof candidate, not increased
accepted coverage or completion of the every-jet goal.

## Formal endpoints

- `LambdaInternal.Local.scalar_lambda_initialized_local_spec_internal` proves
  the existing `secp_jet_initialized_local_spec` for the actual
  `f_simplicity_scalar_multiply_lambda`, with the literal
  `canonical_scalar_multiply_lambda Alg.CoreFunSem` specification.
- `LambdaInternal.Fresh.lambda_runs_from_actual_init_internal` establishes
  execution for every `Word 8` (256-bit) input, starting from the real
  `Genv.init_mem jets_secp.prog`, constructing fresh input/output frames and
  preserving all original initialized-memory loads. It assumes neither an
  execution nor an output nor an already represented global/frame memory.

The local theorem retains the existing startup predicate and every output,
prefix, cursor, load-framing and startup-preservation conclusion. Eight full
printed theorem types, including both fresh-frame witnesses, match the old
results exactly after changing only their theorem names. No domain restriction
or extra final-readability premise was added.

## What changed in the proof

`Graph` proves linkage and internal-call closure for all 24 actual callees.
It reuses the already checked generic internal-execution preservation lemmas.
`State` derives global byte/permission preservation through that graph.
`Calls` tightens the existing real multiplication execution's frame; `Chain`,
`Rest`, `Public`, `Initialized`, `Local` and `Fresh` compose the unchanged
reader, multiplier, writer, entry, source-copy, return and free steps.

Consequently these results no longer depend on
`Events.external_functions_properties` or
`Events.inline_assembly_properties`. The six retained dependencies are recorded
per result in `RUN.json`: classical excluded middle, dependent functional
extensionality, the two inherited real-decision constants, and CompCert's
external-function/inline-assembly semantic parameters. This is not an
axiom-free development. Imported older lemmas still exist with eight
dependencies; they are not used to prove the new endpoints. A recursive kernel
context can therefore contain more axioms than either endpoint depends on.

## Evidence and exact-input limits

`RUN.json` records 19 completed results (six closed, two with four dependencies,
eleven with six), one definition, nine fresh module compilations, eight exact
complete-type comparisons, eight rejected boundary mutations, the original
literal-source correspondence gate and byte-for-byte AST regeneration. Both
the private candidate and main checkout pass the 240-file frozen-target guard.
The report query loads 314 local modules, all in the tracked dependency basis.

At this checkpoint the separate recursive kernel check remains pending.
Only a matching `CHECKED.json` and a successful `verify.py check` certify it.
Scope remains the pinned LP64, assertion-disabled (`RECKLESS`) generated Clight
program and existing initialized local-frame contract, not all configurations
or the evaluator's complete setup/lifecycle.

The basis is `/private/tmp/jet-lambda-internal-basis-g2_0otg0`; the extension is
`/private/tmp/jet-scalar-lambda-internal.gdhGw3` under the sole private namespace
`LambdaInternal`. The source authority is commit
`8d856072668d7364bd014e189fb48168afacebf3`, with frozen production/specification
targets at `91d89bac`. `PREPARATION.json` binds 249 exact source/object pairs
from the checked ordinary beta basis and 134 unchanged, freshly compiled
additional dependencies. No checked parent tree was edited.

One required proof dependency was not committed at that source revision:
`Coq/C/jet_literal_division_parametric.v`. Its exact bytes match the earlier
recorded source hash and the unchanged main proof file. They are archived here
under `inherited/`; `DEPENDENCY-SOURCES.json` identifies this provenance without
claiming that the older receipt remains valid today. The new build and kernel
audit, not that historical receipt, establish verification of this copy.
The user's main proof file and unrelated staged patch are untouched.

The first report attempt terminated because its baseline query omitted an
explicit `Require` for an older theorem's module. `failed-attempt-1/` preserves
the original verifier, query, error and input hashes. The corrected second
attempt has separate launch and log names; the failed launch is not a completed
audit. Earlier preparation failures are retained locally in
`/private/tmp/lambda-internal-prepare-driver{,-2}.log`; only the third
preparation produced the recorded basis.

## Commands

Run from the repository root, with the recorded private trees and pinned
Coq 8.17.1/CompCert 3.14 dependencies available:

```sh
python3 -B proof-work/scalar-lambda-internal/prepare.py check
python3 -B proof-work/scalar-lambda-internal/verify.py kernel
python3 -B proof-work/scalar-lambda-internal/verify.py check
```

Build/report/kernel launch guards prevent silently restarting an existing run.
Do not edit any checked source, object, manifest or verifier in place after the
corresponding receipt has been written. Reproduction on a different basis
requires a new derived tree and new receipts, not reuse of these input-specific
success claims.

Normal acceptance is still separately blocked by the previously demonstrated
frozen Bitcoin primitive-identity/domain discrepancies. This packet does not
alter those targets, bypass their gates or promote a failed normal-acceptance
run. The next independent step is ordinary-module integration of this exact
proof, followed by the existing review/acceptance process when its target
blockers can be resolved with explicit authority.
