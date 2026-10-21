# Alternative field multiplication and square proofs

The 13 `modules/*.v.source` files retain the independent `C.`-namespace proof
from `codex/fe-multiply-parallel` (`ef4aa19c`). The selected active proofs are
`C.jet_secp_multiply_literal_jet` and `C.jet_secp_square_local`. Both approaches
prove the same local contracts over arbitrary inputs, without `memcpy_model`,
and retain the same six inherited execution assumptions. This alternative is
not registered and does not add coverage. The main proofs remain selected
because downstream square and beta work already uses them.

## Registration decision

Keep exactly one active implementation-to-specification proof per jet:

| Public C jet | Selected active endpoint | Claude's archived alternative endpoint |
| --- | --- | --- |
| `simplicity_fe_multiply` | `C.jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec` | `C.jet_parallel_fe_mul_local.fe_multiply_literal_local_spec` |
| `simplicity_fe_square` | `C.jet_secp_square_local.fe_square_local_spec` | `C.jet_parallel_fe_sqr_local.fe_square_literal_local_spec` |

The alternative sources are from `codex/fe-multiply-parallel` at `ef4aa19c`.
Commit `dd4579a7` on `codex/fe-multiply-integration` proposed their registration;
its exact changes are preserved in [unapplied-registration.patch](unapplied-registration.patch).
That registration is not applied to the current branch and must not be merged
over the selected endpoints.

The selection is an integration/maintenance choice, not a claim that Claude's
proof is mathematically invalid or that the selected public contracts are
stronger. Both state the same `secp_jet_local_spec` for the original C functions
and literal Simplicity programs, with arbitrary Word256 inputs and the same
shared frame preconditions. Neither final theorem adds a libc-model premise.
The selected proofs already participate in the accepted build and downstream
proof chains, so replacing them would duplicate integration and verification
without improving the public guarantee.

Only the selected endpoints belong in `Coq/C/jet_coverage.tsv`. The alternative
`jet_parallel_fe_*` modules remain `.v.source` files here, outside both active
Coq project files and the theorem/contract manifests. Keeping this historical
comparison does not keep a second active jet proof or count either jet twice.
Reusable helper lemmas may still be adapted independently; this does not
authorize registering the alternative public endpoints.

`jet_parallel_fe_mul_math.fe_mul_core` proves the original 42-step integer
dataflow with accumulator bounds derived from normalized limbs. The symbolic
executor and its u128 oracles prove actual helper bodies, including shifts by
52 and 64 and in-place aliasing. The multiplication and square models prove
bounded output limbs and the product modulo the field prime. The field,
call and local modules compose these facts with the active reader, wide writer
and allocation/copy/return/free lifecycle.

The original negation dependencies are now active `Coq/C` sources; duplicate
archive copies were removed. `tools/gen_fe_mul_model.py` retains the model
generator and `mul-review/` retains the alternative correspondence checks.
The unapplied registration patch is historical and should not be applied over
the selected main registrations.

To build and kernel-check both alternative endpoints in a fresh external tree,
with Coq 8.17.1 and prepared `JET_DEPS` on the usual environment:

```sh
bash proof-work/fe-multiply-parallel/verify.sh /tmp/parallel-field-check
```

The script uses the committed HEAD, copies the alternative modules into that
external tree and builds their dependencies. Output is printed to the terminal;
redirect it to an external file if needed. It does not change this checkout or
register the alternatives. For the original complete candidate and dependency
metadata see `../README.md`.
