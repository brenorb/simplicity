# jet-discovery

Corpus-driven discovery of missing Bitcoin Simplicity jets (goal: [GOAL.md](GOAL.md)).

**Work in progress:** the registry has 110 rows in 106 distinct groups. [Same-CMR witness aliasing](reports/WITNESS-DATAFLOW.md) invalidated several earlier expressions and their recommendation evidence. Their dataflow is repaired; complete fresh measurements remain required. The toy FRI prototype is retired. The corrected full-size STARK accepts its honest proof at 1,497,462.342 WU; complete corpus metrics are pending. See [current validation evidence](reports/CURRENT-VALIDATION.md).

- **Results:** [reports/RECOMMENDATIONS.md](reports/RECOMMENDATIONS.md) (ranked candidates, per-BIP verdicts),
  [reports/corpus-results.md](reports/corpus-results.md), [reports/whatif.md](reports/whatif.md),
  [reports/subdags.md](reports/subdags.md), [reports/ablations.md](reports/ablations.md),
  [reports/mismatches.md](reports/mismatches.md).
- **Source inventories:** [all open softfork BIPs and proposals](reports/BIP-INVENTORY.md), [eprint scan](reports/eprint-scan.md), [Ethereum/Solana demand](reports/contract-inventory.md), [period rankings and access gaps](reports/PERIOD-RANKINGS.md).
- **New experiments:** [full Fibonacci STARK](reports/FIBONACCI-STARK.md), [STARK resource diagnostics](reports/STARK-DIAGNOSTICS.md), [BN254/Groth16 cost model](reports/bn254-groth16.md), [timed-signature implementation gap](reports/timed-signatures.md).
- **Standard and application coverage:** [FIPS205 SLH-DSA baseline](reports/SLH-DSA-BASELINE.md), [EVICT, BIP322 and SPV applications](reports/BITCOIN-GROWTH.md), [silent payments and BIP127 reserve client](reports/BITCOIN-GROWTH2.md).
- **Method:** [reports/METHOD.md](reports/METHOD.md).
- **Corpus:** [corpus/README.md](corpus/README.md), with [explicit coverage and counting](reports/coverage-and-costs.md). The committed result tables still describe the earlier 49-row run while the expanded corpus is being verified. Sources live in `src/JetDiscovery/Corpus/`.
- **Candidates:** [candidates/](candidates/) (one README per candidate jet).
- **Vendored specs and vectors:** [vendor-specs/MANIFEST.md](vendor-specs/MANIFEST.md).

Everything lives in this directory; no existing file in the repository is changed ([CHANGES_TO_EXISTING.md](CHANGES_TO_EXISTING.md)).

```bash
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run'
```

```bash
nix-shell --run 'cabal test test:tests --test-show-details=direct --test-option=--num-threads=1 --test-option=+RTS --test-option=-N1 --test-option=-M16G --test-option=-RTS'
```
