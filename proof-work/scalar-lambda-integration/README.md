# Normal lambda integration: reviewed preparation

The original `simplicity_scalar_multiply_lambda` proof and its complete selected
closure compile in the normal `C` namespace at
`/tmp/jet-scalar-lambda-integration.mmEs14/Coq`.
The baseline is immutable accepted square (361/533).
Main's proof files, staged edits and coverage registries remain untouched.

`ASSEMBLY.json` records **28 new modules / 116 results / 32 definitions**,
transported only by namespace replacement from six checked archives.
No module is excluded. Reused frame construction is byte-identical to Claude's
finished shared theorem. Old sources and infrastructure remain unchanged except
exact registry/gate extensions and separately reviewed snapshots.

The selected public result is
`C.jet_secp_scalar_lambda_local.scalar_lambda_initialized_local_spec`.
Its initialized-memory contract adds a proved constructible global-state entry
condition and preserves that state; all old output/cursor/prefix/load framing
clauses are exact. It is not an unrestricted-memory old secp contract.
`scalar_lambda_runs_from_actual_init` also constructs logical fresh frames and
executes the original jet for every 256-bit input, starting at actual
`Genv.init_mem jets_secp.prog`. This is not the C evaluator's setup routine.

## Terminal preparation evidence

All checks below exited 0; `PREPARATION.json` pins sources, objects, drivers,
reports and logs.

- Fresh normal compilation: 2229, all 28 modules.
- New assumptions/full contracts: 5388, 116 results / 148 records, 201,971
  untruncated bytes. All scratch counterpart dependency sets match; 60 closed.
- Two-root whole-dependency kernel: 10292, inherited 15-name context,
  unsafe categories empty.
- Snapshot generation: 27372, preparation only.
- Normal review and exact assumption extension: 7044. All 7,299 inherited
  contracts are byte-identical, and all 4,814 inherited dependency sets remain.
  Seven compact printer ellipses have exact untruncated supplements; none
  is omitted or accepted unchecked.
- Eleven normal-review corruption fixtures and 25 public-boundary mutations
  pass, plus coverage/scanner and 240-file production/canonical identity tests.

The new modules are loaded but not opened in the global contract printer, so
new short names cannot change old records. No old contract or axiom is loosened.
The coverage recognizer accepts only this named initialized-state/function
combination; separate source guards pin its whole contract, literal lambda
constant/combinator tree, original dispatch and actual-init/fresh-call witness.

Run read-only checks from the repository:

```sh
python3 -B proof-work/scalar-lambda-integration/review-normal.py --assembly proof-work/scalar-lambda-integration/ASSEMBLY.json
python3 -B proof-work/scalar-lambda-integration/test-review.py
python3 -B proof-work/scalar-lambda-integration/test-lambda-public.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-lambda-integration.mmEs14/Coq
```

The `--prepare-assumptions` mode already completed; do not repeat it.
Reproduce with Coq 8.17.1, CompCert 3.14, VST 2.14, 65520 KiB stack and
`build-jets.sh`. No objects are copied to main.

## Next: full acceptance, then preservation-safe integration

Provisional isolated coverage is **362/533** (258 without an extra library
premise, 104 explicit memcpy-model entries). **Main remains accepted at 361/533.**
Preparation, generated snapshots and kernel roots alone are not full acceptance.

The frozen preacceptance fingerprint is
`0272f0370fbe4a3b6dd73aa21688bc52e0bfd494cbf1c292bf3f12ae85d68616`.
Run the complete `JOBS=1 bash check-jets.sh --accept`, without update/no-build
flags, including all four regenerated AST comparisons. Record its handle and
terminal exit; keep candidate and linked production inputs frozen while live.
Only after terminal success, unchanged fingerprints and post-run review may
the new jet be counted as accepted. Then plan integration preserving every
existing staged/unstaged main edit and verified old contract.

Old main audit 22185 is terminal exit 0; never poll/restart it. Claude's
Elements/environment reservations remain separate. All-533 goal unfinished;
signed atomic local commits only, never push.

