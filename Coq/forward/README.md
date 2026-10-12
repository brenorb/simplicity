# Elements proofs that need forward memory

Branch `claude/shared-obligations`; unregistered.

`simplicity_issuance_token_amount` and `simplicity_current_issuance_token_amount`
call the static helper `issuanceTokenAmt`, whose reissuance branch passes a
stack-allocated compound literal (`&(confAmount){ EXPLICIT, 0 }`) to `amt`.
The helper therefore allocates a block on entry, stores into it between two
output writes, and frees it on return.

The helper contract used by the indexed and current-input theorems is
`write_effect`, which compares **all** loads outside the output ranges.

- Across the stores into the local, `C/jet_elements_effects_local.v` uses
  `write_effect_x bl` (the same relation without the loads of `bl`), which
  composes with ordinary effects and is stable under changes confined to
  `bl`.
- Closing it to a plain `write_effect` around the allocation and release
  needs that the freed block is unreadable afterwards at every offset, i.e.
  that the execution added no permission to it. That is the forward-memory
  property of Clight executions, `clight_exec_forward` of the archived,
  unaccepted `proof-work/sha-support/jet_clight_forward.v.source` (main
  checkout). It is referenced by hash (`startup/PREREQUISITES.sha256`) and
  extracted at build time, not copied.

Modules (`forward/proofs`, logical name `JetForward`):

- `jet_elements_issuance_token_then.v` — the present branch (select the
  record's token amount or build the local explicit zero, then `amt`).
- `jet_elements_issuance_token_helper.v` — `eval_elements_issuanceTokenAmt_layout`.
- `jet_elements_issuance_token_jets.v` — the two jet theorems against
  `primitive IssuanceTokenAmount` (resp. `CurrentIndex >>> assert` of it),
  their executability and `runs_everywhere` statements. The relation only
  requires a token amount in C memory for a *new* issuance.

Build and check: `SHA_SUPPORT=<main>/proof-work/sha-support bash
Coq/build-elements-forward.sh [--check]` (the Elements modules of `Coq/C`
must be compiled first).

Assumptions: the six inherited ones plus, through the forward lemma,
`Events.external_functions_properties` and
`Events.inline_assembly_properties` — the eight already inherited by the
accepted SHA-unit results.
