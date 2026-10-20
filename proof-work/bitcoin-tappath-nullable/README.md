# Nullable Bitcoin tappath contract candidate

The accepted tappath theorem is sound but its environment relation is too
restrictive for a real empty-path builder result: it always requires a
non-null CompCert path pointer. The production builder stores NULL for zero
path length; the original jet only reads the path pointer in the in-range
branch. No C or canonical specification change is needed.

This archive independently checks Claude's additive resolution, preserved
byte-for-byte from local signed commit
`09060a1b112e681f96d31505694b45572ee7c462`, and adds the raw-spec wrapper
and formal boundary regressions. It does **not** modify the accepted relation
or registry, accept the broader builder proof chain, or add another jet.

## Checked results

- `bitcoin_tappath_nullable_local_spec`: original complete C jet execution,
  including wrapper entry/copy/cleanup, current-memory loads, both branches,
  output, cursor and framing; the path-pointer load premise is conditional on
  non-empty path length. The exact existing Simplicity primitive is retained.
- `bitcoin_tappath_nullable_raw_local_spec`: same execution through the
  existing canonical raw-environment projection, not an independent cache
  specification. The inherited raw tap-path length bound remains at 128.
- `bitcoin_tappath_env_rep_weaken` and `bitcoin_tappath_env_rep_nonempty`:
  old environments are supported, and non-empty-path contracts are equivalent.
- `bitcoin_tappath_nullable_empty` and `bitcoin_tappath_nullable_raw_empty`:
  empty-path relation establishment requires only the taproot pointer and
  length loads, with no path-pointer load or value premise. Thus NULL is not
  excluded. Separation from the output is still supplied by the jet contract.
- `bitcoin_tappath_empty_cells` and `bitcoin_tappath_empty_sem`: every Word8
  index on an empty path returns the sum's absent branch; 256 payload cells
  are unspecified, as skipBits promises, not assumed to be initialized.
- `bitcoin_tappath_old_rep_rejects_null`: formal negative check for the old
  contract, including bounded-offset injectivity. The failure is a contract
  domain restriction, not an implementation correctness counterexample.

## Verification

Fresh explicit compilation of both modules and the two audit drivers exited
zero. An independent whole-dependency kernel check, started after the final
rebuild with sources frozen, exited zero. Nine full types, one full definition,
and all assumption records are hash-pinned along with the compiled artifacts.
Two results are closed; five representation results retain four inherited
classical/extensionality dependencies; the two execution roots retain those
plus CompCert's two semantic parameters. No new axiom. The inherited kernel
context has 15 axioms; all three unsafe categories are empty.

The production source identity check passed (240 files) and the Bitcoin
canonical primitive identity check passed (eight extended constructors).
Full AST regeneration and the integrated acceptance gate were **not** run.
Registry promotion and independent builder-chain verification remain pending.
The unrelated dirty registry/range/SHA/field-negate work is untouched.

The recorded runs used a 150-second process bound for each compiler and a
300-second kernel bound. Rebuilding requires fresh evidence receipts; do not
mistake a prior `.vo` or this receipt for verification of changed sources.

## Integration sequence

1. Promote the exact first source as `C.jet_bitcoin_tappath_nullable`, retaining
   the old module and relation for compatibility with existing consumers and
   Claude's weakening/builder lemmas. Change the raw adapter's single
   `NullableC` import to `C` in the derived integration tree, then rebuild it.
2. Register both modules, all nine results and the nullable definition in an
   isolated reconciled candidate. Select `bitcoin_tappath_nullable_raw_local_spec`
   for the existing `simplicity_bitcoin_tappath` coverage row. This strengthens
   one existing jet's domain; it must not increase the jet count.
3. Generate and review exact contract/definition/assumption differences,
   including the guarded pointer load, unchanged hash/length/frame premises,
   and unchanged inherited dependencies. Freeze inputs and run full acceptance
   without update flags. Do not accept the currently dirty unrelated snapshots
   as a side effect of this small integration.
4. Independently check Claude's
   `Coq/bitcoin-env/C/jet_bitcoin_env_relations_tappath.v:ready_tappath_nullable`
   and the builder dependency chain. Its real-builder footprint chooses
   `(bE,176,176+32*length)` even for an empty path; this is accepted by the
   nullable relation. Our independent empty constructor chooses a zero-sized
   `(bt,0,0)` interval, so do not confuse those two witnesses.
5. Compose builder establishment with the raw relation and jet frame contracts.
   The builders use a derived translation unit: establish the necessary common
   program linkage/transport before claiming a single end-to-end caller-to-jet
   execution. This archive alone does not prove malloc success, cached hashes,
   builder lifecycle or evaluator dispatch.
