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

`C/bitcoin/exec.c` takes the per-input budget as a parameter
(`simplicity_bitcoin_execSimplicity(..., minCost, budget, ...)`).  The only
fixed limit in this repository is `BUDGET_MAX = 4000050` WU
(`C/limitations.h:9`).  How Bitcoin would compute a spend's budget is not
defined here.  Bitcoin Core's integration is not in this repository.

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
fixed. Hypothetical jets have no assigned consensus encoding, so their changed
program length and any resulting budget change cannot be measured here. A
before/after fit is therefore conditional on that fixed scenario, not a Bitcoin
deployment claim.

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
it.  Groups are reported only if they are repeated (multiplicity ≥ 2, or found
in ≥ 2 programs), cost at least 1 WU per instance, and are not already a single
jet.  Nested groups overlap, so shares do not add up.

## Verification-burden estimates

For each candidate, `candidates/*/README.md` names the closest existing jet
whose C implementation was proven equivalent to its Simplicity specification
on the `feat/jet-equivalence` work.  This was read-only: no proof work was
done here.  The burden estimate (low / medium / high) is a judgement based on
that analogy.  It is not a measurement.

## Biases and limits

**The corpus is written by one author against one library.**
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
[FIBONACCI-STARK.md](FIBONACCI-STARK.md); its full-size honest diagnostic has
a measured cost, while complete corpus/report validation remains separate.

**Non-native curves use witness hints.** The P-256 and ed25519 programs take
s⁻¹ mod n and decompression x-coordinates as witness and check them, as a
compiler targeting Simplicity would.  Computing them in-script would cost more.

## Source coverage and counting

The BIP inventory inspects every nonterminal softfork row at its pinned
revision, including exclusions. The eprint log is complete for the stated
metadata queries, with automated and individually reviewed verdicts kept
separate. The contract inventory preserves both all-category holdings and
non-CEX TVL rankings, plus explicitly bounded single-block gas/CU sources;
those blocks do not replace unavailable 24-hour explorer rankings.

Registered testable rows, distinct counting groups, complete spend conditions,
complete bounded verifiers, protocol components, and arithmetic kernels are
separate quantities in `coverage-and-costs.md`. Parameter and equivalent-path
variants do not fill the 150-program target. A complete spend condition does
not implement a protocol's off-chain setup, liveness, or foreign consensus.
