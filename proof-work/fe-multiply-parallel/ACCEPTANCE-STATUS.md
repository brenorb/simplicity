# Acceptance status of the fe_multiply / fe_square registration

Branch `codex/fe-multiply-integration` (from `feat/jet-equivalence` `d4677f3d`,
merges `codex/fe-multiply-parallel`). Registration is committed; the reviewed
snapshots (`C/jet_assumptions.expected`, `C/jet_contracts.expected`,
`C/jet_coqchk_axioms.expected`) are NOT updated.

## Blocker (baseline, not introduced here)

Repository-wide `check-jets.sh --update-expected` / `--accept` cannot pass on
any tree derived from `d4677f3d`:

* Update 2026-10-19: after merging `feat/jet-equivalence` `2472cb0c`,
  `jet_bitcoin_count_bridge.v` is repaired upstream (`7f2d7382`) and compiles;
  `jet_bitcoin_value_domain.v` still fails. See `BITCOIN-BLOCKER-PROPOSAL.md`
  and `HANDOFF.md` (the user chose the main agent's fe_multiply/fe_square
  proofs for registration).
* `C/jet_bitcoin_value_domain.v` and `C/jet_bitcoin_count_bridge.v` did not
  compile against the pinned original `Coq/Simplicity/Primitive/Bitcoin.v`
  (`sigTxiValue_bound` cannot be inferred; `Not convertible`). Reproduced in a
  clean export of `d4677f3d` (see `$S/base-bitcoin.log` in the run notes) and
  documented in `proof-work/original-target-boundary/README.md`.
* `check-bitcoin-primitive-identity.py` (and the tests depending on it) fail
  with `Bitcoin base primitive name mismatch: LockTime` identically on the
  baseline.

Both are owned by the main agent; changing those theorems or relaxing the gate
is out of scope.

## What passes on this branch

* All other static checks, including `jet-coverage.py` (351/533) and
  `test-jet-coverage.py`, and the new `mul-review` gate (13 reviewed
  definitions/propositions, 41 mutations rejected).
* Full `-k` build: only the two Bitcoin modules above fail; two `Timeout!`
  failures under `-j12` load (`jet_secp_u128_layout`, `jet_copyBits_two_words_left`)
  are being rebuilt at `-j3`.
* Earlier fresh isolated runs of the proof branch: build, report and recursive
  coqchk exit 0, axioms equal the allowlist (`evidence-41dac7e2/`).

## Remaining

1. Main agent fixes or retires the two Bitcoin modules and the identity gate.
2. Then run `scoped-acceptance.sh` or directly `check-jets.sh --update-expected`,
   review that the diff contains only the 135 new theorem / 158 definition
   records and no new axiom name, and run `check-jets.sh --accept`.
