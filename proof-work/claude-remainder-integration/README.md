# Review of the remaining Claude support

Frozen local source: `claude/shared-obligations` at
`30404face45383153528f36d915de6d7df11f3f4`. No remote writes.

This driver reviews four copied, isolated proof closures: common/Elements
candidates, Bitcoin environment readiness/startup, Elements SHA/startup,
and Elements environment helpers/callers. Each substituted translation unit
gets its own `C` namespace. Original broad build scripts are not used to
overwrite the main tree. Registries and coverage are deliberately unchanged.

`BASELINE.json` pins all existing Coq/C/Haskell audit inputs and the unrelated
staged patch. Each installed batch has `ASSEMBLY.json`, `REVIEW.json` and
`INSTALLATION.json`. Review requires frozen source provenance, a fresh build
of new modules, exact regenerated ASTs, complete type/definition/assumption
reports, and recursive `coqchk` with no unchecked kernel flags. Installation
adds files only. `post-check` checks preserved inputs and all saved artifacts.

The `seal` step only binds already completed audit evidence to its assembly
and revalidates it; it does not perform or claim a new compiler/kernel run.
Review corruption tests mutate reads in memory, never compiler inputs.

Run with the pinned Coq 8.17.1/CompCert 3.14 environment:

```sh
ulimit -s 65520
python3 -B proof-work/claude-remainder-integration/run.py prepare --group GROUP
python3 -B proof-work/claude-remainder-integration/run.py check --candidate /absolute/candidate
python3 -B proof-work/claude-remainder-integration/run.py seal --candidate /absolute/candidate
python3 -B proof-work/claude-remainder-integration/test-review.py /absolute/candidate
python3 -B proof-work/claude-remainder-integration/run.py install --candidate /absolute/candidate
python3 -B proof-work/claude-remainder-integration/run.py post-check
```

## Review boundaries

- Elements jet proofs target the existing Coq primitive-semantics port.
  Only the previously admitted primitive clauses have canonical Haskell
  source review. Importing candidates adds **zero accepted jets**.
- `rsort_model` is a contract definition, not a verified radix-sort
  implementation. The Elements transaction builder remains incomplete;
  committed helpers do not imply a proof of its whole body.
- `memcpy_exact` uses CompCert's defined builtin memory-copy semantics.
  The plain-byte loop additionally requires initialized data bytes. Neither
  result identifies the original external libc function with that reference.
- Forward-memory lifting uses the two inherited CompCert external-function
  property assumptions in addition to the usual six; this does not expand
  the normal registry's assumption policy.
- Bitcoin startup establishment is conditional on successful
  `Genv.init_mem`; preservation requires separation from the SHA globals.
  Readiness is about the derived environment unit, not yet an execution
  theorem for the original evaluator/jet dispatch. Supplied transaction-id
  bytes are copied, not computed or validated.
- The three linked-program definition-list lemmas contain unchecked proof
  casts in the frozen branch. Those modules and their consumers are not
  integrated as verified results. The secp constructibility extension also
  reaches an existing unchecked normalization lemma and is excluded.
- Existing startup results already transported into main are not duplicated
  unless needed as a dependency of a new program-specific startup proof.
- A group receipt is not a combined full-normal-worktree acceptance receipt.
  No goal-completion claim follows from these support additions.

Batch completion and exclusions are recorded separately in `STATUS.md`.
