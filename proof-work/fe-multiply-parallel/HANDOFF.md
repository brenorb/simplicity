# Handoff to the main agent (2026-10-19)

**Decision (user):** register the main agent's own `fe_multiply`
(`proof-work/secp-field-*`) and `fe_square` (`C.jet_secp_square_local.fe_square_local_spec`,
`proof-work/secp-square-*`) proofs. This branch's proofs stay as a
checked alternative and are **not** to be registered alongside them.

Branches (local, signed, not pushed):

* `codex/fe-multiply-parallel` (`ef4aa19c`): the alternative proofs
  (`Coq/C/jet_parallel_fe_*`, 13 modules) and fresh-isolated evidence
  (`evidence-41dac7e2/`: build, report and recursive coqchk exit 0; axioms equal
  `jet_coqchk_axioms.expected`).
* `codex/fe-multiply-integration`: merged with `feat/jet-equivalence` `2472cb0c`.
  Do **not** merge `dd4579a7` (it registers these duplicates). Possibly useful:
  * `41a1dc70` lists 11 committed but unlisted `u128` helper modules
    (`jet_secp_umul128_*`, `jet_secp_u128_*`, `jet_secp_u64_carry`) in both
    project files;
  * `BITCOIN-BLOCKER-PROPOSAL.md`: concrete options for the remaining
    acceptance blockers (`jet_bitcoin_value_domain.v`, LockTime identity gate).
    The user asked for a proposal only; nothing was changed.

Reusable pieces if wanted, for example for `fe_multiply_beta` or other secp jets
using the `u128` helpers:

* `jet_parallel_fe_mul_oracle.v`, `jet_parallel_fe_mul_shift.v`: proved
  fresh-word oracles for `u128_mul`, `u128_accum_mul`, `u128_accum_u64` and
  `u128_rshift` (52, 64). A whole `fe_mul`/`fe_sqr` run takes under 1 s.
* `jet_parallel_fe_mul_math.v` (`fe_mul_core`): closed integer dataflow theorem,
  also reused for squaring with b = a.
* `Coq/mul-review/` on the integration branch: source gate and 41 mutations for
  the FeMultiply/FeSquare catalog, programs, contracts and C bodies.
