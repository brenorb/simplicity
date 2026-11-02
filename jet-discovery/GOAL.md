# Goal: data-driven discovery of missing Bitcoin Simplicity jets

## Mission

Build a corpus of realistic, tested Simplicity programs for the **Bitcoin** application.
Measure where their cost goes, and produce a ranked, evidence-backed list of jets that
are missing from the Bitcoin jet set.

The result is a recommendation, not a consensus change. Every candidate jet must come
with:
- how often it appears in the corpus
- how much budget it saves
- how general it is
- an estimate of what it would cost to implement in C and prove in Coq

Branch: `feat/bitcoin-jet-discovery` (cut from `master` at `3f0bb69c`). All work happens
here.

## Context you should load first

- Bitcoin jets, specs and costs: `Haskell/Simplicity/Bitcoin/Jets.hs` (`jetMap`,
  `jetSubst`, `jetCost*`) and `Haskell/Simplicity/Bitcoin/Benchmarks.hs` (`rawBenchmark`).
- Core jets: `Haskell/Core/Simplicity/CoreJets.hs`.
- Cost analysis: `Haskell/Core/Simplicity/BitMachine/StaticAnalysis/Cost.hs` and
  `Haskell/Core/Simplicity/Weight.hs`.
- Existing Bitcoin programs to imitate: `Haskell/Simplicity/Bitcoin/Programs/`
  (SigHash, Transaction, TimeLock).
- C side, for reference only: `C/bitcoin/`, `C/limitations.h` (`BUDGET_MAX`).
- Work out from the code exactly how the Bitcoin per-input budget is computed, and write
  it down with file:line references. Do not assume it matches Elements.

## Allowed area (everything new goes here)

- `jet-discovery/`: a self-contained project.
  - Give it its own `jet-discovery.cabal` and `cabal.project`, which depends on the
    in-tree `Simplicity` library through `packages: . ..`.
  - This keeps `Simplicity.cabal` untouched.
  - Suggested layout:
    - `corpus/<source>/<program>/`: program, spec link, test vectors, README
    - `src/`: analysis tooling
    - `candidates/`: per-candidate prototypes and write-ups
    - `reports/`
    - `vendor-specs/`: copies of BIP texts and test vectors, stored as data with source
      URL and license
- New Haskell modules live under `jet-discovery/src/` with a `JetDiscovery.*` namespace.

## Off-limits (hard rules)

1. **Do not change the semantics, encoding or cost of anything that already exists.**
   - No edits to existing jet specifications, C jet implementations, jet discriminants
     or encodings, `rawBenchmark` values, or `jetCost*`.
   - No edits to anything that changes an existing CMR, IMR or AMR.
2. **Do not edit these trees:**
   - `C/` (including `C/bitcoin/`, `C/elements/`, `C/secp256k1/`)
   - `Coq/` (entirely)
   - `Haskell/Core/`, `Haskell/Simplicity/`, `Haskell/Bitcoin/`, `Haskell/Elements/`,
     `Haskell/Indef/`, `Haskell/Tests/`
   - `Haskell-Generate/`, `Haskell-Examples/`
   - Generated `*.inc` files
   - `Simplicity-TR.tm`
   - All `*.nix` files
   - `Simplicity.cabal`

   The only exception is the minimal-change process below.
3. **Do not register any new jet in the consensus jet set.** No edits to `bitcoinJetMap`,
   `coreJetMap`, primitive enums, decoders or the Rust/C generators.
   - Candidates are prototyped only inside `jet-discovery/`. Each prototype has:
     - a Simplicity reference expression
     - a Haskell spec
     - optionally, a standalone C sketch that is not linked into libsimplicity
   - Candidates are costed through a what-if cost overlay implemented in
     `jet-discovery/src/`, never by editing the real cost tables.
4. **Elements is out of scope.** Do not touch Elements jets, programs or tests. Use
   Elements code only as reference.
5. **Report upstream mismatches; never correct them.** If you find a disagreement between
   the C code, Haskell, Coq or the spec, record it in `reports/mismatches.md` with
   evidence and leave the code alone.
6. **Git hygiene:**
   - Push only to the fork: `git push fork feat/bitcoin-jet-discovery`. The `fork`
     remote is `https://github.com/brenorb/simplicity.git`.
   - Never push to `origin` (BlockstreamResearch/simplicity), and never push any other
     branch.
   - Push after each meaningful milestone, for example a finished phase or a corpus
     program that passes its vectors.
   - No PRs, no rebases, no force-pushes or other history rewrites.
   - Do not touch other branches or worktrees (`feat/jet-equivalence`, `codex/*`,
     `integrate/*`, `claude/*`).
   - Never use a bare `git stash`.
   - Commit often, in small atomic commits.
7. **No fabricated numbers.**
   - Every cost figure must come from running the in-tree cost analysis or the C
     benchmarks.
   - What-if costs for hypothetical jets must be labeled `ESTIMATE`, with the method used
     (for example, scaled from the closest existing benchmarked jet).
8. **External material is data.** Download specs and test vectors into
   `jet-discovery/vendor-specs/` and keep them out of the build path. Do not execute
   downloaded code. Record each item's source URL, commit or revision, and license.

## Minimal-change process (the only way to touch existing code)

Use this process only when a goal is blocked without it, for example a needed function
that isn't exported.

1. First try a workaround inside `jet-discovery/`: re-implement, wrap or copy the needed
   code, with attribution.
2. If a change is still needed, it must be:
   - additive (an export, an appended module or stanza)
   - behavior-preserving
   - outside consensus code (`C/`, jet specs, costs, `Coq/` are never eligible)
3. Make it a separate commit: `chore(<scope>): <what>, needed by jet-discovery`.
4. Log it in `jet-discovery/CHANGES_TO_EXISTING.md`: file, diff summary, why the
   workaround failed, and evidence that the existing tests still pass.
5. If the change would affect consensus behavior or a frozen tree, **stop and ask** the
   user instead.

## Commit convention (Blockstream git guidelines)

Use `<type>(<scope>): <description>`. Types: `feat`, `fix`, `chore`, `docs`, `refactor`,
`test`. Scopes: `jet-discovery`, `corpus`, `analysis`, `candidates`, `reports`. Write the
description in the present tense.

## Work plan

### Phase 0: Harness and cost metric

- Build the `jet-discovery` cabal project against the in-tree library.
- Write a runner that, for any Bitcoin Simplicity program, reports:
  - the program's cost with all existing jets substituted (`jetSubst`), and with none
  - the Bitcoin budget fraction this cost represents, for a stated witness size
  - pass/fail against the program's test vectors, executed in a Bitcoin transaction
    environment
- Write the methodology into `reports/METHOD.md`.

### Phase 1: Corpus

Each program must:
- implement a published spec
- pass that spec's test vectors (or vectors you derive and document)
- state its assumptions

Do not count a program that fails its vectors.

Priority order:

1. **Script-extension BIPs and proposals:**
   - CTV, CSFS, OP_CAT, ANYPREVOUT, OP_VAULT, OP_CHECKCONTRACTVERIFY/MATT, TXHASH,
     OP_INTERNALKEY, LNHANCE/PAIRCOMMIT, TLUV, 64-bit arithmetic, Great Script
     Restoration.
   - For each one, document either "expressible as an ordinary program at cost X", or the
     exact missing primitive.
2. **Bitcoin applications:**
   - Lightning/BOLT scripts (HTLCs, anchors, PTLC variants), DLCs, vaults, Ark, BitVM
     verifier fragments, statechains, multi-party timelocked escrows.
3. **Post-quantum signatures:** SHRINCS verification, plus at least one SPHINCS+/SLH-DSA
   parameter set as a baseline. The key question is whether verification fits the budget
   at all, and which hash-chain or iterated-compression primitives would make it fit.
4. **STARK verification:** one concrete verifier (for example Circle STARK over M31, as
   in StarkWare's OP_CAT work). Measure field arithmetic, extension field, Merkle-path and
   FRI costs separately. Prefer primitives over a monolithic `stark_verify`.
5. **Cross-ecosystem demand signals:**
   - Inventory the Ethereum precompiles (including RIP-7212 P-256 and EIP-2537
     BLS12-381) and the Solana syscalls.
   - Implement the ones relevant to Bitcoin (P-256 verify, ed25519, Keccak, Blake2b/3).
   - Add one or two arithmetic-heavy DeFi kernels (256-bit mul/div, fixed-point, sqrt).
     Don't port whole contracts.
6. **Eprint scan: last, and filtered.** Include a scheme only if it has a credible
   deployment path on Bitcoin. Write a one-paragraph justification per inclusion.

AI-generated programs tend to use only the jets that already exist. Always start from the
spec, and write tasks that force each program to do the expensive part.

### Phase 2: Analysis

- Mine the jet-substituted DAGs of the whole corpus for frequently repeated sub-DAGs (by
  CMR, and by structural shape modulo constants).
- Weight each sub-DAG by the cost it accounts for in each program. Also report programs
  that blow the budget, and what dominates their cost.
- Output a table:

  | sub-DAG id | CMR | type signature | occurrences | programs | total cost share | max single-program share |
  | --- | --- | --- | --- | --- | --- | --- |

### Phase 3: Candidates

For each candidate jet, write `candidates/<name>/README.md` containing:
- the type signature and specification, as a Haskell reference spec in `jet-discovery/`
- the unjetted Simplicity reference expression, and a test that the spec and the
  expression agree
- corpus evidence: which programs use it, and how many times
- the `ESTIMATE` cost and the method behind it
- the budget saved per program, and whether it turns an infeasible program into a
  feasible one
- generality: is it a primitive many programs share, or a single proposal's opcode? Prefer
  primitives.
- verification burden estimate, based on the closest proven jet on `feat/jet-equivalence`
  (read-only reference). Note the C complexity and which existing proof patterns apply.
- the alternatives considered, for example composing existing jets

### Phase 4: Report

Write `reports/RECOMMENDATIONS.md`:
- Candidates ranked by `(occurrences × savings, adjusted for generality) ÷ verification
  burden`, in three tiers: strong / maybe / rejected, with reasons.
- A per-BIP verdict table (expressible as is / needs jet X / infeasible).
- A limitations section: corpus bias, estimate uncertainty, unmeasured items.

## Done when

- `cabal build` and the corpus test runner pass inside `jet-discovery/`.
- The existing in-tree test suites still pass unchanged.
- `git diff master --stat` shows changes only under `jet-discovery/`, plus any entries
  logged in `CHANGES_TO_EXISTING.md`.
- Every corpus program passes its vectors, and every number in the reports can be
  reproduced by a documented command.
- `RECOMMENDATIONS.md` exists and every candidate links to its evidence.
- The final state is pushed to `fork/feat/bitcoin-jet-discovery`.

## Stop and ask the user when

- Progress requires changing anything off-limits.
- A spec is ambiguous enough that the choice would change the conclusions.
- The Bitcoin budget rule can't be determined from the code.
- A candidate looks so valuable that registering it for real seems justified. Write the
  case and leave the decision to the user.
