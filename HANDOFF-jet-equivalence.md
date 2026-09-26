# Handoff: arithmetic jet equivalence

Updated 2026-09-26. Work locally on `feat/jet-equivalence`; commit small,
verified units and do not push. Read
[/Users/brenorb/.codex/skills/coq-proof-engineering/SKILL.md](/Users/brenorb/.codex/skills/coq-proof-engineering/SKILL.md)
and its Clight reference before adding execution proofs.

## Goal status

The active milestone—prove the actual generated C/CompCert Clight bodies for
`increment_16`, then `add_16`, equivalent to their canonical Simplicity jet
specifications—is complete. Both are proved from initial-memory/frame
contracts, with no assumed helper executions or successful stores. Do not
restart the reader, carry/wide writer, dependency setup, or these two proofs.

The goal is specifically implementation-to-specification equivalence for
individual jets. It does not claim mathematical correctness of the Simplicity
specifications, evaluator-wide substitution, small-step uniqueness, or
compiled machine-code correctness. No admits, new proof axioms, unchecked
casts, or informal proof substitutes were used.

| Result | Established scope |
| --- | --- |
| `jet_one8_layout.v`, `jet_increment8_layout.v`, `jet_add8_layout.v` | Complete individual jet calls for arbitrary non-wrapping layouts, including crossings and initial-memory contracts. |
| `jet_one_wide_layout.v:eval_one_wide_layout_matches_spec` | Complete `one_16`, `one_32`, and `one_64` calls via `W16/W32/W64`. |
| `jet_read16_layout_exec.v:eval_read16_layout_non_crossing` | Actual `read16`, exact logical Word16 value, arbitrary addresses/word indices and non-crossing cursor remainders. |
| `jet_read16_layout_exec.v:eval_read16_layout_crossing` | Actual `read16` for crossing remainders 49..63, deriving the intermediate memory/cursor facts. |
| `jet_write_wide_layout_total.v:eval_write_wide_layout` | Actual wide writers for all long payloads; permissions, output observation, prefix/range and memory framing. |
| `jet_increment_wide_word.v:increment16_values_denote_input` | Closed symbolic arithmetic bridge from C carry/payload to the canonical increment specification. |
| `jet_increment16_layout.v:eval_increment16_layout_matches_spec` | Complete generated `increment_16` call for arbitrary valid non-wrapping cursors, crossings, unrelated input bits, and initialized output contents. |
| `jet_add16_wide_word.v:add16_values_denote_input` | Closed symbolic arithmetic bridge to `Word.adder 4`; C carry is the unsigned `(65535-y) < x` comparison. |
| `jet_add16_layout.v:eval_add16_layout_matches_spec` | Complete generated `add_16` call for consecutive Word16 inputs and arbitrary valid non-wrapping cursors, including crossings. |

The frame API requires descriptor blocks and backing-storage blocks to be
distinct. The checked generated C/AST configuration is x86-64 Linux LP64,
little-endian PRODUCTION: ordinary/static assertions are enabled, while
production debug-assert guards are false. Fully debug-enabled execution is
not covered. Generation uses the real C sources and pinned Debian headers;
see [JET_PROOFS.md](Coq/C/JET_PROOFS.md).

## Proof architecture and reuse

The reusable decomposition validated by `increment_16` and `add_16` is:

1. Express the logical input as selected MSB-first frame bits.
2. Prove the actual C reader returns the exact unsigned input value and
   preserves the required frame/memory properties.
3. Prove a width-specific symbolic arithmetic bridge from actual C values to
   the canonical Simplicity program.
4. Adapt the generated Clight body with its exact temporaries/types and
   compose reader, arithmetic, carry/payload writer, and frame lifecycle.
5. State the public theorem only in terms of initial-memory conditions; derive
   helper executions and every store inside the proof.

For another width, reuse the frame lifecycle, logical-bit predicates, wide
writers and carry-plus-wide output contracts. Keep small adapters for
width-specific generated readers/jet bodies and prove corresponding symbolic
arithmetic lemmas. Parameterize genuinely shared bit/word structure, but avoid
a broad framework rewrite until additional complete consumers demonstrate the
right abstraction. `Word n` has width `2^n`; e.g. Word16 is `Word 4`.

ABI details matter: generated 16/32/64-bit reader results are `Vlong`, while
read8 returns `Vint`. For 64-bit arithmetic, the carrier sum can wrap; use
modular sum semantics together with the separately computed carry rather than
assuming the machine sum is the unbounded integer sum. The next natural
follow-on is `increment_32` and `add_32`, then the corresponding 64-bit jets;
these are not yet proved and are outside the completed W16 milestone.

The crossing reader proof also surfaced durable tactics lessons: use one
normal form for equivalent cursor arithmetic; prove exact unsigned values and
range facts when C comparisons rely on them; isolate closed shift/count
obligations; and do not reduce symbolic memory or enumerate payload values.

## Verification environment and commands

Dependencies were rebuilt locally (outside the repository): CompCert v3.14 at
`/tmp/simplicity-compcert-rebuilt` and VST v2.14 tag checkout at
`/tmp/simplicity-vst-rebuilt`. The VST tag's internal version metadata says
2.13 and pins CompCert 3.13; its build succeeded with CompCert 3.14 using
`IGNORECOMPCERTVERSION=true FLOCQ=bundled`. Coq is 8.17.1 in the `simplicity`
opam switch. If those temporary checkouts are removed, rebuild dependencies
before attempting project verification; do not regenerate the C AST unless
its inputs change.

From repository root:

```sh
env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  COMPCERT=/tmp/simplicity-compcert-rebuilt \
  VST=/tmp/simplicity-vst-rebuilt \
  opam exec --switch=simplicity -- bash Coq/build-jets.sh -j2

env OPAMROOT=/Users/brenorb/.opam-simplicity-root \
  COMPCERT=/tmp/simplicity-compcert-rebuilt \
  VST=/tmp/simplicity-vst-rebuilt \
  opam exec --switch=simplicity -- bash Coq/build-jets.sh \
  --coqchk -silent C.jet_add16_layout C.jet_increment16_layout
```

The full build compiles all listed jet modules and the assumption audit.
`Print Assumptions` reports inherited CompCert/Simplicity execution
assumptions; inspect it rather than treating it as an automatic axiom gate.
Both pure arithmetic bridges are `Closed under the global context`. The
full build and `coqchk` above passed after both public theorems were added.

## Checkpoints

- `41d86fa` / `7ff3ef9`: increment16 Clight adapter and complete equivalence.
- `5a94026` / `799fe53` / `59d3c34`: add16 arithmetic bridge, Clight adapter,
  and complete equivalence.
- `6a646ad`: general crossing read16 proof; `coqc` and `coqchk` passed.
- Final full `build-jets.sh -j2` and assumption audit passed; final
  `coqchk -silent C.jet_add16_layout C.jet_increment16_layout` passed.

The review's abandoned, unverified crossing experiment is at
`/tmp/simplicity-handoff-review.3oJwDG/read16-crossing-unverified.patch` and
must not be reapplied. The user's separate untracked `jet-proof-review.patch`
is user-owned and must remain untouched/unstaged.
