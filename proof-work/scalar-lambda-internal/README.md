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

## Commands

Run from the repository root, with the recorded private trees and pinned
Coq 8.17.1/CompCert 3.14 dependencies available:

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
