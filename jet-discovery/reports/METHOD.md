# Method

How every number in `reports/` is produced, and what it does and does not mean.

## Reproducing

From `jet-discovery/`:

```bash
nix-shell --run 'cabal build all'
```

```bash
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run'
```

```bash
nix-shell --run 'cabal test --test-show-details=direct --test-option=--num-threads=1 --test-option=+RTS --test-option=-N1 --test-option=-M12G --test-option=-RTS'
```

`run` executes every corpus program on its test vectors, measures it, and rewrites
`reports/corpus-results.md`, `reports/subdags.md`, `reports/whatif.md`,
`reports/ablations.md` and `reports/data/*.tsv`.  It exits non-zero if any
vector fails.  The earlier 49-row run took about 20 minutes on an 18-core machine. The larger corpus includes substantially heavier verifiers; that timing is no longer a prediction.

Other commands:
- `run <prefix>` runs a subset.
- `verify <prefix>` checks vectors and same-CMR stability without measuring costs or producing analysis checkpoints.
- `stark-reference` generates and checks the full-size Haskell proof without constructing a Simplicity DAG.
- `profile <id>` prints a program's most expensive sub-DAGs.
- `time <id>` times the measurement phases.
- `metadata` exports every registered entry's complete metadata as TSV without
  constructing proofs or Simplicity terms; `index` regenerates the corpus index.
  Write metadata to a temporary file and move it after a successful exit.

Eligible single-witness entries use [prepared kernels](PREPARED-KERNELS.md) for
batch functional evaluation. Every vector still checks its exact typed source
fingerprint and composed jetted CMR; internal witnesses/delegation or mismatches
take the canonical whole-program path. Static analysis and serialization always
consume the complete original expression. The result note identifies actual
prepared evaluation. `tools/run_recorded.py NAME -- COMMAND ARGS...` freezes a
local executable and preserves output, source hashes and actual exit status for
long validation jobs; source hashes describe the launch checkout, not compiler
attestation.

The toolchain comes from `jet-discovery/shell.nix`.  It uses the GHC package
set of the in-tree `../default.nix`, plus `cabal-install`.  The in-tree
`Simplicity` library is built from source as a local package
(`cabal.project`: `packages: ./ ../`).  No file outside `jet-discovery/` is
modified.

To check the unchanged upstream suites with their default QuickCheck case
count and no name filter, use:

```sh
nix-shell --run 'python3 tools/check_upstream.py'
```

The script archives the committed `C/` tree into ignored build storage before
`make check`, and enables the Haskell suite through a separate project file.
Its source and declared optimization settings stay unchanged. An explicit
RTS link flag permits a bounded heap; logs, exact commands, source-tree hashes,
project hash and actual exit statuses are retained in `reports/data/`.
The earlier disabled-suite, compiler-tick and unlinked-RTS attempts are
retained as build diagnostics, not passing upstream tests.

## Long-run checkpoints and resource use

The final full-corpus path uses a fresh process for each exact registered ID:
`python3 tools/run_isolated.py --runner <built-executable> --label <cohort> --heap 64G`.
Build all library/executable/test targets first and freeze source/spec/vector
files throughout the cohort. The coordinator copies the executable once to
an immutable hash-named path. That same path and byte hash, plus the strict
global source fingerprint, bind every child and the final aggregation.
Each child runs `run-one <exact-id>`; prefix matches are rejected. The full-run fingerprint is published only
after all output tables have been rendered and the source fingerprint still
matches. A failed render leaves no current publish marker. The coordinator verifies
that marker and hashes every published table in its terminal manifest.
`--last <exact-id> ...` can defer expensive runs without dropping any registry
row; use the same order on resume. A new full cohort refuses an existing
checkpoint namespace for that fingerprint. Preserve an earlier namespace
separately if intentionally remeasuring; an explicit resume reuses only its
recorded, hash-checked results. Every new full-cohort child must log exactly
one passing outcome per registered vector. Full-run inputs must be tracked
and match `HEAD`; the cohort records the start commit. The final audit checks
for identical commitment roots across groups. The only reviewed exception is
the deliberately disconnected default versus APO sighash pair documented in
[DISCONNECTED-SIGHASH.md](DISCONNECTED-SIGHASH.md). Heap size
is a runtime resource cap, not a changed mathematical parameter.

Checkpoints live under `dist-newstyle/jet-discovery-results/<fingerprint>/`.
They retain all numeric costs, candidate counts/scenarios, typed profiles,
CMRs, ablations and vector outcomes as plain data. Both vector names and
expected outcomes must match the current entry, in order; equal counts alone
are insufficient. Profile-total/root consistency and all outcomes must pass.
Namespaced paths prevent another preliminary binary from overwriting a final
row. Source/executable hashes are checked before and after children and the
cohort; actual exit, log SHA256, checkpoint SHA256 and elapsed time are saved.

The final `aggregate` command refuses any missing, stale or failing row and
never compiles a fallback expression. It loads all verified compact profiles
for complete mining and report generation. The two small BIP341 cost-only
stand-in variants remain measured there and are never executed. This process
boundary lets an individual program share a complete transform DAG without
retaining that graph while another program runs. Global hashing and all
vector/measurement checks remain intact; no per-entry cache weakening or
serialized expression substitution is used.

`--only` is explicitly development coverage and never generates the full
reports. A recorded arithmetic control and its `--resume` pass are under
`data/isolated-control-arithmetic/`; strict rejection of missing rows without
rewriting existing reports is in `data/isolated-strict-aggregation-rejection.json`.
The separate3GiB baseline control exhausted its heap during primitive-only
analysis (`data/isolated-control-baseline/`), so it receives no pass credit.
The42-test source includes same-length vector-name and expectation-mismatch
regressions, with the targeted completed check in
`data/isolated-checkpoint-header-guards.{txt,json}`. The source-mtime check is
an additional stale-build guard; it is explicitly not compiler attestation.

The runner logs every measurement phase and every actual vector outcome.
Before evaluating vectors it fully forces the saved profile's hashes, shape,
costs, multiplicities, node counts and types; the compact record can then
release the typed source DAG instead of retaining lazy field closures until
checkpoint serialization. This changes evaluation order, not the expression
or cost formulas. The complete ChaCha20 check
`data/chacha-complete-analysis-progress.{txt,json}` preserves all12 passes
and the identical canonical CMR,2,258,812milliWU native bound and5,773total
program+witness bits from the earlier diagnostic. Both runs remain
pre-final evidence; neither supplies fresh whole-corpus coverage.

`run` and `run <prefix>` save plain-data measurement/profile checkpoints under
`dist-newstyle/jet-discovery-results/` after each program. A completed row can
be reused only when its fingerprint matches all current local sources,
vector/spec data, in-tree Haskell/C inputs, build settings and executable,
and its vectors and profile consistency checks pass. Saving and re-reading
also releases closures retaining source DAGs. Interrupted rows rerun. Delete
that generated directory to force fresh measurements.

Use `+RTS -N1 -A16m -M64G -RTS` for a sequential analysis with a bounded heap
on the full STARK; smaller programs can use smaller caps. The corrected
full-size honest diagnostic reached 43.0 GB live Haskell heap constructing
the typed DAG. This changes resource use, not the static cost, and does not
measure evaluator RAM required by a consensus implementation.
The first full STARK run with concurrent analyses was killed; the 6 GiB
sequential attempts also failed during DAG construction. Exact diagnostics
are in [STARK-DIAGNOSTICS.md](STARK-DIAGNOSTICS.md). A failed run supplies no
measured cost row and never counts as a passing program.

## Corpus programs

Each program is a Bitcoin Simplicity expression `term () ()`, written with the
in-tree Haskell library (`Simplicity.Programs.*`,
`Simplicity.Bitcoin.Programs.*`).  It is parameterised by its witness data
(`JetDiscovery.Types.Entry`).

Programs use library expressions whose form matches existing jet
specifications.  `jetSubst` then finds the jets inside them, exactly as it would
for a program a user publishes.

**Vectors.** Every program carries test vectors: a transaction environment, a
witness and an expected outcome.

- A vector is executed on the jet-substituted program with `fastEval`.
  Substitution changes the CMRs that `disconnect` commits to, and the
  jet-substituted program is the one a spender would publish.
- A program counts only if every vector, positive and negative, gives the
  expected outcome.
- The runner also checks that a program's CMR does not depend on its witness.

**Operands as witness data.** Where a proposal is an opcode, its operands
(public key, message, committed hash) are witness data.  The program then
measures the opcode's work with one CMR for all vectors.  In a real script some
operands would be constants, which changes costs only marginally: a 256-bit
constant through the constant-word jet costs about 0.3 WU.

**Bounds.** Simplicity has no unbounded loops.  Loops over inputs, outputs and
buffers are unrolled to stated bounds, given in each program's assumptions
(`reports/corpus-results.md`).  The static cost bound is computed for the
worst case of those bounds, whatever the actual transaction looks like.

## Cost

**The static bound.**
- **Cost (WU)** is the static CPU cost bound of the jet-substituted program:
  `TermWeight`, the same bound that `simplicity_analyseBounds` in C/eval.c
  checks against the budget.
- `JetDiscovery.Profile` recomputes the bound node by node from the
  type-annotated DAG of `jetDag`, with each jet priced at
  `Simplicity.Bitcoin.Jets.jetCost` (benchmark-derived).  The runner checks that
  the per-node recomputation sums to exactly `TermWeight`.
- `case` takes the more expensive branch.

**Cost columns.**
- **Prims-only baseline:** the same program with only the jets that wrap a
  single transaction primitive, plus constant words
  (`JetDiscovery.JetSets.PrimOnly`).  Bitcoin Simplicity exposes primitives
  only through jets, so this is the cheapest jet set in which every program is
  still expressible.  For anything with elliptic-curve arithmetic the baseline
  is astronomically large (about 10^17 WU).  It shows that jets are mandatory,
  not how much a given jet saves.
  The implementation reconstructs the shared existing-jet DAG through the
  public type checker, expands removed specifications and reruns whole-program
  substitution/type inference. Ablations use the same route. Tests compare
  this with direct substitution of the original source, including an ignored
  half-word whose witness/copy width can shrink after a projection jet is
  removed. No fixed per-jet cost sum substitutes for that inference.
- **Ablations (`reports/ablations.md`):** the program with one family of
  existing jets removed (`JetDiscovery.JetSets.Ablate`):
  - secp256k1 curve and signature jets,
  - all secp256k1 jets,
  - SHA-256 jets.

  These are measurements of programs that do exist.
- **What-if (`reports/whatif.md`):** the program with candidate jets added
  (`JetDiscovery.WhatIf`).
  - A candidate's specification is a corpus kernel, so the overlay replaces
    every occurrence of it, matched by identity Merkle root.
  - A candidate's cost is an **ESTIMATE**, scaled from the benchmark of the
    closest existing jet, with the method stated
    (`JetDiscovery.Candidates.Registry`, `candidates/*/README.md`).
  - Candidates whose specification needs data Simplicity cannot express (BIP
    341 precomputed hashes) are estimated with cost-only variant programs that
    use stand-in jets of analogous cost (`JetDiscovery.Candidates.Variants`).
    Those variants are measured but never executed.
- **Isolated candidates (`reports/candidate-impact.md`):** one candidate at a
  time with all existing Bitcoin jets. The shared combined-overlay DAG is
  reconstructed through the public type checker, every other candidate is
  expanded to its reference, and full-program type inference/substitution runs
  again. This preserves nested matches, type erasure and branch changes.
  A conservatively computed candidate dependency closure skips only candidates
  absent from every branch, including inside collapsed candidate expressions.
  Independent full-source substitution tests cover nested ecrecover/Keccak,
  unused Keccak padding and competing branches. Fixed per-jet deltas would
  miss copy/witness cost changes when a removed jet frees unused type widths.
  The complete matrix, including zero matches, is in `data/candidate-impact.tsv`.
  Savings from different rows are alternatives and must not be summed.
  The WOTS frontends are one primitive family when ranking generality/demand.

**Unit.** Costs are in weight units (WU).  `Simplicity.Bitcoin.Benchmarks`
scales jet benchmarks so that `CheckSigVerify` costs 50 WU (after a 0.5
batch-verification adjustment that applies to the signature-verification jets
only), and every combinator adds 0.1 WU of overhead.  Candidate ESTIMATEs use
the same `cost` function.

## Budget (open question)

[`C/bitcoin/exec.c:44–46`](../../C/bitcoin/exec.c#L44-L46) takes the
per-input budget as a caller parameter. [Lines 125–129](../../C/bitcoin/exec.c#L125-L129)
cap that input before analysis. The fixed ceiling is 4,000,050 WU
([`C/limitations.h:9`](../../C/limitations.h#L9)). The repository does not
contain the Bitcoin Core integration or a rule deriving this budget from a
transaction.

So reports give:
- the absolute static bound;
- its share of `BUDGET_MAX`;
- the result under an **ASSUMPTION**: a BIP 342-style budget equal to the
  witness stack size in bytes plus 50 WU (`JetDiscovery.Run.witnessBudgetModel`).

The hypothetical four-element witness stack is serialized as:

> CompactSize(4) + sum(CompactSize(element length) + element length)

Its element lengths are program bytes, witness bytes, 32 (CMR), and 33 (a
single-leaf control block). CompactSize boundaries are included rather than
assuming one byte per prefix. This stack layout and budget formula are both
assumptions, not an established Bitcoin spending format. The table reports
the WU deficit for programs that do not fit; it supplies no valid witness
padding procedure or claim that arbitrary trailing data would be accepted.
Candidate feasibility holds this original serialized stack's assumed budget
fixed and caps the comparison at the in-tree maximum. The candidate-impact
TSV preserves the raw assumption, the maximum, and their minimum. Hypothetical jets have no assigned consensus encoding, so their changed
program length and any resulting budget change cannot be measured here. A
before/after fit is therefore conditional on that fixed scenario, not a Bitcoin
deployment claim.

Program and witness lengths are point measurements of the first vector in
each entry. The CMR excludes witness values, but serialized witness encoding,
constant sharing and variable-buffer length can change with those values.
The displayed hypothetical budget therefore describes that measured vector,
not every witness accepted by the same CMR. No universal fit claim follows
from an empty-message or zero-filled first vector.

Entries whose assumptions begin `CLIENT MODE:` verify an offchain statement
using an explicitly supplied environment. Their cost remains useful as a
computational comparison, but budget-fit fields are `n/a (client verifier)`.
The candidate-impact TSV marks feasibility inapplicable for them. Rankings
must disclose client-only evidence separately from native spending demand;
pure component/kernels likewise do not acquire full-application weight.

Jet rankings do not depend on the budget rule.  Feasibility statements do, and
they are labelled as depending on the assumption.

## Mining (Phase 2)

`JetDiscovery.Mine` groups the nodes of every program's profile across the
corpus in two ways:
- by actual 256-bit commitment Merkle root (`niCmr`), computed node by node using the in-tree commitment tags and public jet interface;
- by shape (`niShape`: constant word values ignored, so the same kernel with
  different constant indices coincides).

Every profile root CMR must equal the library-computed program CMR, and its self-cost sum must equal `TermWeight`; either mismatch fails the run. CMRs exclude witness values and, except for jets, type annotations, so exact groups can carry multiple type signatures. Shape identifiers remain structural 64-bit hashes, with their representative CMR disclosed; they are heuristic mining keys rather than cryptographic identities.

Each group's **total** is the sum over programs of multiplicity × the
sub-DAG's static bound.  That is the part of the corpus's cost spent inside
it. The Markdown table shows each program's selected-path occurrence count
and inclusive WU. The exact and shape TSVs store semicolon-separated
program-ID/count pairs in programs and program-ID/inclusive-mWU pairs in
program_inclusive_mwu. Both pair formats use a colon delimiter. Their per-program
inclusive mWU add to total_mwu. The maximum single-program share uses the
combined weight of all the group's type instantiations in that program.
Groups are reported only if they are repeated (multiplicity ≥ 2, or found
in ≥ 2 programs), cost at least 1 WU per instance, and are not already a single
jet.  Nested groups overlap, so shares do not add up. [Budget hotspots](budget-hotspots.md)
uses exclusive profile weight times multiplicity, including unique nodes,
to partition the native bound for each non-client over-budget program.

## Verification-burden estimates

The final isolated-scenario ranking is reproduced with
`python3 tools/rank_candidates.py --runner <same-frozen-full-run-executable>`.
The executable's `fingerprint` command must match the successful full run's
`data/run-fingerprint.txt`; missing, partial or stale output is rejected.
Its `candidates` command supplies all 23 frontend prices and their exact
benchmark-analogue methods. Registry/vector/classification coverage and every
cell of the isolated candidate matrix are checked before writing anything.

`data/candidate-ranking-policy.json` records ordinal generality/proof-burden
judgements and context weights, rather than measured proof hours. Original
bounds already include occurrence multiplicity, so isolated bound savings
are not multiplied by occurrences a second time. Each counting group receives
at most one contribution per candidate family, selecting the largest positive
isolated saving among variants/frontends. The two WOTS frontends share one
family. This conservative envelope is not a measurement of composing both
frontends. Raw individual rows, including zero matches and negative savings,
remain in the primary per-candidate tables. `matched_dag_nodes` counts
distinct matched nodes across all branches, with shared nodes counted once.
The `occurrences` field counts multiplicity only on the selected worst path
after repricing. A candidate can reduce the original worst branch until
another branch sets the bound; the report and score retain positive savings
even when the new path has zero occurrences. Native full predicates, client
verifiers and components/kernels have separate displayed savings; client-only
evidence cannot silently become native onchain demand. Tier decisions remain
explicit policy judgements requiring review of the fresh evidence.

After ranking, review the measured match concentration, budget scenarios and
implementation/proof tradeoffs. Record each final tier and reason in the policy
JSON, then run `python3 tools/publish_recommendations.py --runner <same-frozen-full-run-executable>`.
This verifies the complete run again, requires 150 distinct groups and a
majority of full applications/verifiers, and inserts the exact isolated
matches in every candidate README. The final recommendations include the
complete numbered and unnumbered proposal verdicts. Stale fingerprints and
pending tier decisions cannot replace the current reports.

For the final audit, export `corpus-metadata.tsv` from the frozen runner (or
copy the cohort's exact `registry.tsv`). After publication, run:

```sh
python3 tools/check_final_evidence.py --cohort <isolated-manifest.json> --harness <unfiltered-tests-run.json>
```

The audit checks each exact entry log and local checkpoint hash, all core
and derived publication hashes, tested source/data, actual upstream results,
every candidate README and source table, and the Git scope. Run it in the
original measurement checkout with its frozen executable and ignored
checkpoints; the signed logs and publication manifests remain portable. The
fork update is independently verified after the signed final push.


For each candidate, `candidates/*/README.md` names the closest existing jet
whose C implementation was proven equivalent to its Simplicity specification
on the `feat/jet-equivalence` work.  This was read-only: no proof work was
done here.  The burden estimate (low / medium / high) is a judgement based on
that analogy.  It is not a measurement.

## Biases and limits

**The corpus uses one library and one set of modeling conventions.**
- Programs use the library's existing jets wherever they can, which can
  understate gaps the library hides.
- Specs were chosen to force the expensive work: exact BIP serializations,
  variable-length messages, post-quantum verification.

**Static bounds are worst cases.**
- WOTS+C chains are counted at 15 steps each, although the constant sum makes
  verification do 240 steps in total.
- Loops are counted at their bound, not at the actual input count.
- Real CPU time is lower.  The budget is enforced on the bound.

**Estimates are not benchmarks.** Every ESTIMATE needs a C implementation and a
benchmark before it means anything for consensus.

**The SHRINCS vectors are derived.** SHRINCS publishes its test vectors only as
SHA-256 fingerprints.  The vectors here come from a Haskell transcription of
the spec's Python, so a misreading shared by the transcription and the program
would not be caught.

**The earlier circle-FRI program is retired.** Its historical toy-parameter
and extrapolated costs belong to a builder with unbound copied witnesses and
are withdrawn. Trace/composition openings and the DEEP quotient were also
absent. The corrected full Fibonacci AIR/DEEP/FRI experiment is described in
[FIBONACCI-STARK.md](FIBONACCI-STARK.md). The full-size eight-vector
diagnostic and the complete corpus run are separate evidence; use the
complete run's fingerprint for comparisons across programs.

**Non-native curves use witness hints.** The P-256 and ed25519 programs take
s⁻¹ mod n and decompression x-coordinates as witness and check them, as a
compiler targeting Simplicity would.  Computing them in-script would cost more.

## Source coverage and counting

Regenerate [all per-source comparisons](coverage-and-costs.md) with
`python3 tools/coverage_report.py --runner <same-frozen-full-run-executable>`.
The explicit runner must reproduce the complete analysis fingerprint and the
exported metadata; every result/vector count and client/budget row is checked
before publication. With no runner, the inventory and verdicts are still
available but show costs as pending. Numbered and unnumbered proposal rows
are available separately in [bip-verdicts.md](bip-verdicts.md).

The BIP inventory inspects every nonterminal softfork row at its pinned
revision, including exclusions. The eprint log is complete for the stated
metadata queries, with automated and individually reviewed verdicts kept
separate. The contract inventory preserves both all-category holdings and
non-CEX TVL rankings, the complete single-block/single-slot execution
samples, an independent full Ethereum UTC day of receipt gas, and the
provider-reported Soltop rolling 24-hour slice. Etherscan and Solscan
period tables were unavailable. The alternative sources have different
windows, coverage and attribution rules; see [PERIOD-RANKINGS.md](PERIOD-RANKINGS.md)
and the [Ethereum UTC day](ETHEREUM-DAY-GAS-RANKING.md).

Registered testable rows, distinct counting groups, complete spend conditions,
complete bounded verifiers, protocol components, and arithmetic kernels are
separate quantities in `coverage-and-costs.md`. Parameter and equivalent-path
variants do not fill the 150-program target. A complete spend condition does
not implement a protocol's off-chain setup, liveness, or foreign consensus.
