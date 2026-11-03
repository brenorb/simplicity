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
nix-shell --run 'cabal test'
```

`run` executes every corpus program on its test vectors, measures it, and rewrites
`reports/corpus-results.md`, `reports/subdags.md`, `reports/whatif.md`,
`reports/ablations.md` and `reports/data/*.tsv`.  It exits non-zero if any
vector fails.  A full run takes about 20 minutes on an 18-core machine.

Other commands:
- `run <prefix>` runs a subset.
- `profile <id>` prints a program's most expensive sub-DAGs.
- `time <id>` times the measurement phases.

The toolchain comes from `jet-discovery/shell.nix`.  It uses the GHC package
set of the in-tree `../default.nix`, plus `cabal-install`.  The in-tree
`Simplicity` library is built from source as a local package
(`cabal.project`: `packages: ./ ../`).  No file outside `jet-discovery/` is
modified.

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

The witness stack is estimated as:

> program bytes + witness bytes + 32 (CMR) + 33 (control block for a single leaf) + 4 length prefixes

Under this assumption a program that does not fit must pad its witness.  The
padding is reported.

Jet rankings do not depend on the budget rule.  Feasibility statements do, and
they are labelled as depending on the assumption.

## Mining (Phase 2)

`JetDiscovery.Mine` groups the nodes of every program's profile across the
corpus in two ways:
- by exact structure (`niHash`: combinator, types and constant values);
- by shape (`niShape`: constant word values ignored, so the same kernel with
  different constant indices coincides).

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

**Full-size STARK costs are extrapolated.** A complete circle-FRI verifier is
measured at toy parameters (2^8 domain, 6 folds, 3 queries); full-size costs
scale its per-query-layer cost to 30 queries and 20 layers and are labelled
ESTIMATE.  Trace and composition openings and the DEEP quotient are not
included.

**Non-native curves use witness hints.** The P-256 and ed25519 programs take
s⁻¹ mod n and decompression x-coordinates as witness and check them, as a
compiler targeting Simplicity would.  Computing them in-script would cost more.
