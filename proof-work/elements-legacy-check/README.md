# Original-C legacy Elements relative-lock assertions

Two further whole-C implementation-to-specification proofs are complete, but
not yet normally registered: `broken_check_lock_distance` and
`broken_check_lock_duration`. These are assertions: C's false return corresponds
to specification failure, not an assumed successful comparison.

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

That read-only command additionally pins the historical main-399/index state
used during checking. Once main advances, preserve these receipts as historical
evidence rather than rerunning that obsolete exact-main check on a successor.
The original staged-patch SHA-256 remains
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.

Normal registration, full normal acceptance and installation are separate next
steps. These two proofs add no registered coverage yet. The every-jet goal is
unfinished.
