# Lambda: fresh frames and initialized public boundary

The original `simplicity_scalar_multiply_lambda` now has both:

- `scalar_lambda_runs_from_actual_init`: for every 256-bit input, actual
  `Genv.init_mem jets_secp.prog` succeeds, fresh represented input/source/output
  frames exist, and the original Clight jet returns the literal canonical
  Simplicity result, preserving initialized state and every pre-existing load.
- `scalar_lambda_initialized_local_spec`: the full existing secp local
  output/cursor/prefix/load-framing contract on arbitrary represented frames,
  with initialized readonly lambda memory required and preserved.

The latter uses a new initialized-memory contract. Removing only its Ready
entry/postconditions recovers the old contract exactly; no old contract is
edited, and the original unrestricted-memory contract is not claimed.

## Reuse and the diagnosed permission direction

The 343-line shared frame constructor is reused **byte-for-byte** from Claude's
`Coq/C/jet_frame_constructible.v` (last-file commit `e8e5500a`; source hash
`bea74aa2c91ed29613b9a986b002a691eaefdfdfac32d7c1b6d2da40bcf08255`).
No work in the sibling worktree or shared registries was edited.

That constructor promises that final old-block permissions imply initial
permissions, not the converse. The new bridge derives final readability from
the four preserved **actual Mint64 loads**, then obtains the exact readonly
bounds from backwards permissions. No final-readability premise is added.

Fresh-frame setup is a logical CompCert-memory construction, not execution of
the C evaluator's allocator/setup routine. The arbitrary-frame theorem remains
conditional on represented frames and initialized globals, and preserves the
latter for subsequent calls. No execution, result, free or initialization fact
is assumed.

## Checks and scope

Five modules / 16 results / seven definitions explicitly rebuilt through Qed.
Build 85671, assumptions 66430, contract inspection 49efbb and two-root
whole-dependency kernel 80964 all exited 0. The 23 full records occupy 21,899
bytes without ellipses. Five results are closed, eight inherit the existing
four classical parameters, and three inherit all eight existing Coq/CompCert
parameters. Kernel context matches the inherited 15-name allowlist; unsafe
categories are empty. There is no new axiom or explicit libc-model premise.

Run `python3 -B proof-work/scalar-lambda-frames/review.py` and `test-review.py`.
Reproduce with Coq 8.17.1, 65520 KiB stack and the immutable multiplication base's
`build-jets.sh`; reuse the parent's seven narrow scratch mappings and add
`-Q /tmp/jet-scalar-lambda-frames.v7rTNY LamFrameC`.
Compile the five modules in manifest order, then both drivers. Both the fresh
and local modules must be kernel roots: neither imports the other.

These archived sources are **unregistered scratch evidence**. Accepted main
coverage stays **361/533**, including 104 explicit memcpy-model entries.
Main audit 22185 is terminal exit 0; do not poll/restart it. Next promote the
reviewed closure to normal C namespaces, add a narrowly guarded initialized
public contract with source wiring and corruption tests, inspect snapshots,
then run full isolated acceptance before claiming new coverage.

Signed atomic local commits only; never push. All-533 goal remains unfinished.

