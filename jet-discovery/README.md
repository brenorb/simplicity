# jet-discovery

Corpus-driven discovery of missing Bitcoin Simplicity jets (goal: [GOAL.md](GOAL.md)).

- **Results:** [reports/RECOMMENDATIONS.md](reports/RECOMMENDATIONS.md) (ranked candidates, per-BIP verdicts),
  [reports/corpus-results.md](reports/corpus-results.md), [reports/whatif.md](reports/whatif.md),
  [reports/subdags.md](reports/subdags.md), [reports/ablations.md](reports/ablations.md),
  [reports/mismatches.md](reports/mismatches.md).
- **Method:** [reports/METHOD.md](reports/METHOD.md).
- **Corpus:** [corpus/README.md](corpus/README.md) (25 programs; sources in `src/JetDiscovery/Corpus/`).
- **Candidates:** [candidates/](candidates/) (one README per candidate jet).
- **Vendored specs and vectors:** [vendor-specs/MANIFEST.md](vendor-specs/MANIFEST.md).

Everything lives in this directory; no existing file in the repository is changed ([CHANGES_TO_EXISTING.md](CHANGES_TO_EXISTING.md)).

```bash
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run'
```

```bash
nix-shell --run 'cabal test'
```
