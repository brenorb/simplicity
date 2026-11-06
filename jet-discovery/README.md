# jet-discovery

Corpus-driven discovery of missing Bitcoin Simplicity jets. [Research goal](GOAL.md)

The complete corpus run passed all **2,698 vectors** across **157 registered
programs** in **150 distinct groups**. **108 groups** are full bounded spend
conditions or verifiers. The analysis covers **23 candidate frontends in 22
families** and retains **335 source rows** across the proposal and contract
inventories. [Terminal cohort](reports/data/isolated-final-157-lf/manifest.json)
[Local validation](reports/data/final-validation.json)
[Publication hashes](reports/data/recommendations-publication.json)

- **Results** [Ranked recommendations and proposal verdicts](reports/RECOMMENDATIONS.md),
  [per-program costs](reports/corpus-results.md), [combined overlays](reports/whatif.md),
  [isolated candidate costs](reports/candidate-impact.md), [over-budget cost drivers](reports/budget-hotspots.md),
  [sub-DAG mining](reports/subdags.md) and [ablations](reports/ablations.md).
- **Source inventories** [Per-source verdicts and costs](reports/coverage-and-costs.md),
  [open soft-fork BIPs and unnumbered proposals](reports/BIP-INVENTORY.md),
  [ePrint scan](reports/eprint-scan.md), [Ethereum and Solana demand](reports/contract-inventory.md),
  [period rankings and access gaps](reports/PERIOD-RANKINGS.md) and
  [Ethereum precompiles and Solana syscalls](reports/CROSS-ECOSYSTEM-INTERFACES.md).
- **Verifier studies** [Full Fibonacci STARK](reports/FIBONACCI-STARK.md),
  [BN254 and the Groth16 arithmetic estimate](reports/bn254-groth16.md),
  [FIPS205 SLH-DSA](reports/SLH-DSA-BASELINE.md) and
  [verifiable timed signatures](reports/timed-signatures.md).
- **Implementation and evidence** [Corpus specifications and vector scope](corpus/README.md),
  [candidate prototypes](candidates/), [vendored specs and vectors](vendor-specs/MANIFEST.md),
  [validation and archived development runs](reports/CURRENT-VALIDATION.md),
  [upstream mismatches](reports/mismatches.md) and [method and limitations](reports/METHOD.md).

Native costs are static bounds. Hypothetical jet prices and savings are
estimates, and the witness-size fit calculation applies a stated budget
scenario. Client verifiers are listed separately from on-chain spend
conditions. The STARK is a custom M31-family proof profile with open
soundness and wire-interoperability questions. The BN254 study measures
field arithmetic and extrapolates a bounded pairing arithmetic scenario.
The ePrint inventory records the retrieved metadata and its full-text review
gaps. The Ethereum UTC-day ranking and the Soltop provider sample retain
their distinct windows, metrics and missing Etherscan or Solscan datasets.
[Method and limitations](reports/METHOD.md)
[Ranking scope](reports/PERIOD-RANKINGS.md)

The task branch changes files only under `jet-discovery/`.
[Scope record](CHANGES_TO_EXISTING.md)

## Verify the signed reports

Run this command from this directory at the signed report commit.

```sh
python3 -B tools/check_final_evidence.py --published-only \
  --cohort reports/data/isolated-final-157-lf/manifest.json \
  --harness reports/data/harness-final45.json
```

This checks the signed source and handoff history, archived logs, report
hashes and the published STARK checkpoint and stage costs. The default
audit additionally checks the original frozen executables and all local
checkpoints and recomputes the path-bound fingerprint. Run the default
audit in the measurement checkout. [Verification method](reports/METHOD.md#verification-burden-estimates)

## Reproduce the run

From this directory in a clean checkout, build the runner, choose a new
cohort label, and keep all measured inputs frozen until strict aggregation.

```sh
nix-shell --run 'cabal build all test:tests'
reproduction_runner=$(nix-shell --run 'cabal list-bin exe:jet-discovery')
python3 tools/run_isolated.py --runner "$reproduction_runner" --label reproduced --heap 64G
```

A fresh checkout produces its own fingerprint because the executable path
is part of that hash. The method describes test execution, controlled resume,
ranking review and final publication against the new terminal manifest.
[Reproduction method](reports/METHOD.md)
