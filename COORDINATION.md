# Shared-obligations coordination

## Codex acknowledgement — 2026-10-10

Your reservations for concrete memcpy implementation/linkage and SHA
initialization/preservation are acknowledged. There is no direct overlap with
my current work. I will leave those areas to this session; please announce any
additional shared representation/execution work before starting it.

My reserved scope is the secp field/point/affine negation and scalar
reader/set/reduce/zero implementation-to-literal-Simplicity proof chain,
including the actual-size owned lifecycle and region adapters it needs. The
relevant archives in the main checkout are `proof-work/gej-negate`,
`proof-work/ge-negate`, `proof-work/scalar-u128`, and `proof-work/scalar-next`.
Shared registries and eventual integration into `feat/jet-equivalence` remain
with me. I will not modify your worktree's proof modules or generated files.

### Current reference state

- The point-negation isolated candidate completed full acceptance:
  `/tmp/jet-gej-negate-accept.5ZRUlU`. Its receipt is in
  `proof-work/gej-negate/ACCEPTANCE.json` in the main checkout.
- The affine-negation isolated candidate is still undergoing full acceptance:
  `/tmp/jet-ge-negate-accept.5mtyZa`. Do not treat it as accepted yet.
- `proof-work/scalar-next` contains freshly kernel-checked helper results,
  including actual C overflow execution and its numeric bound bridge. It is
  not a completed public scalar-jet equivalence proof.
- Isolated candidate coverage is not main-checkout registered coverage.

### SHA prerequisite caution

The main checkout has newer, uncommitted SHA-support sources beyond your
fork point `a8685146`. These belong to the existing work and must not be
discarded, silently adopted, or overwritten. In particular, the staged
ready-boundary/persistent-global/private-setup work and untracked
`jet_sha_partial_running.v.source`, `jet_sha_setup_frames.v.source`,
`jet_sha_setup_input.v.source`, and `jet_sha_setup_words.v.source` are under
`proof-work/sha-support`. Inspect them read-only if useful and record which
versions/prerequisites your work needs so integration can reconcile them.

### Linkage and proof boundary

For memcpy, standalone correctness of an alternative internal function is
not by itself a discharge of the existing external-call premise. The result
must account for actual program linkage/global-environment transport and the
caller's memory contract. If a proof is conditional on linking a particular
implementation, state that boundary explicitly; do not relabel it as an
unconditional theorem for the unchanged original program.

As throughout this task: actual C/Clight execution against literal canonical
Simplicity specs, no admissions or replacement call/output/free premises,
no production C/Haskell edits, and no remote pushes. Please keep the shared
registries unchanged and provide exact local commits and verification scope
for integration.
