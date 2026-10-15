# Original-C legacy Elements relative-lock assertions

Two further whole-C implementation-to-specification proofs are complete, but
not yet normally registered: `broken_check_lock_distance` and
`broken_check_lock_duration`. These are assertions: C's false return corresponds
to specification failure, not an assumed successful comparison.

Private tree: `/private/tmp/jet-elements-legacy-check.9hQr9l`.
Input SHA-256:
`ef21d973d3eb6b828497afda77ac20aa27ac0891e74a48510dc800e2b916b57b`.
Its predecessor is the completed legacy-getter proof tree, not a live audit's
object cache. All inherited source bytes remain unchanged. The single new
module, `C.jet_elements_legacy_check`, has eight results and five definitions.
Three results are closed; both whole-C endpoints have exactly the six inherited
project assumptions, with no added library model or assumed helper execution.

## What is proved

The literal specification is the canonical Elements assertion over the input
and legacy all-input relative-lock getter, followed by Word16 comparison.
The proof composes actual C function entry, frame copying, `read16`, transaction
field loads, the obsolete-lock helper, unsigned comparison, return conversion
and freeing locals. It derives both success and failure and preserves original
memory in either case. On success it also establishes the zero-output frame
and cursor/prefix contract. No desired comparison or execution is a public
premise.

The C `uint_fast16_t` carrier is 64-bit on this generated target. The reader
therefore supplies exact unsigned representation, not merely equality after
lossy Word16 decoding. `exec_elements_checked_helper_rest` shares the actual
reader/helper/comparison structure across reader widths; concrete shape lemmas
retain each generated function's identity.

The inherited initial environment relation still requires the cached legacy
maximum to agree with the logical inputs, and the represented version and
readable fields. This batch does not prove construction of those caches by
`env.c`. LP64/RECKLESS, representation and canonical host-library boundaries
remain explicit.

## Completed checks

Fresh compilation, full type/definition and assumption reports, direct Elements
AST regeneration and recursive `coqchk` passed (41260, exit 0). `CHECKED.json`
binds source, object, commands and logs. No admissions, assumed declarations or
unchecked casts are used.

Independent review finished as 44828, exit 0: canonical/source correspondence,
32 assertion/failure/cache/whole-C source corruptions and 32 independent
proof/evidence corruptions passed. `EVIDENCE-REVIEW.json` binds the completed
checker and all review tools/logs. Review covers the full partial contracts,
not just a successful tactic prefix or a mathematical relationship between
specifications.

```sh
python3 -B proof-work/elements-legacy-check/review.py review /private/tmp/jet-elements-legacy-check.9hQr9l
```

That read-only command additionally pins the historical main-399/index state
used during checking. Once main advances, preserve these receipts as historical
evidence rather than rerunning that obsolete exact-main check on a successor.
The original staged-patch SHA-256 remains
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.

Normal registration, full normal acceptance and installation are separate next
steps. These two proofs add no registered coverage yet. The every-jet goal is
unfinished.
