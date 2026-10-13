# Bitcoin executability and environment construction — second shared batch

Six modules are imported byte-for-byte from Claude's local commit
`30404face45383153528f36d915de6d7df11f3f4`:

- `jet_env_rep_stable`: existing Bitcoin environment relations survive fresh
  frame allocation and stores in other blocks.
- `jet_app_executable_registry`: execution on fresh frames for the 36 original
  registered Bitcoin application contracts, given a represented environment.
- `jet_bitcoin_env_constructible{,_indexed,_distance,_raw}`: construction of
  represented logical environments and 36 `runs_everywhere` results, removing
  memory/frame/environment premises. Raw results retain the existing
  tap-path-length bound of 128.

These compose the already checked complete C jet contracts with constructive
memory witnesses. They do not assume execution or output in their final
results, do not prove the actual C environment builders, and do not remove
the canonical logical environment's existing domain/representation bounds.
They add no new jet to coverage.

The original tappath executability/constructibility result is deliberately
retained for compatibility; it constructs a non-NULL witness even for an empty
path. The independently checked nullable contract is the domain improvement
for actual callers. Migrating its coverage row does not retroactively change
the original 36-instance generated module or its theorem types.

## Verification

The batch reuses the first integration's audit implementation, now supporting
`--batch`. Its manifest selects the eleven prerequisite modules plus these
six, all freshly compiled in normal `C` namespaces. Recorded scratch:
`/tmp/jet-shared-foundations.2_446d_9`.

Fresh compilation of all 17 modules and the full type/definition/assumption
driver, followed by whole-dependency independent kernel checking, exited 0.
There are 251 results (160 new) and 37 definitions (four new); 36 results are
closed. Remaining result assumptions are the existing four/six-name sets.
The inherited 15-name kernel context is unchanged, with all three unsafe
categories empty. The manifests pin sources; `REVIEW.json` pins every new
object, driver, log and result assumption set.

```sh
ulimit -s 65520
python3 -B proof-work/shared-foundations-integration/check.py --batch proof-work/bitcoin-support-integration --build
python3 -B proof-work/shared-foundations-integration/check.py --batch proof-work/bitcoin-support-integration
python3 -B proof-work/shared-foundations-integration/test-check.py
```

This is an explicit, separately checked support target, not normal public
registry admission or whole-jet acceptance. The ordinary jet build does not
select these six modules yet. The main registries and unrelated staged edits
remain untouched by this import. Nullable tappath normal admission is handled
separately in `../nullable-admission/`, through reviewed snapshots and full
acceptance of an isolated candidate.

No production C, canonical specification, generated AST or existing proof
body is changed. No linked reference-libc or Elements proof is included.
Local signed commits only; no pushes.
