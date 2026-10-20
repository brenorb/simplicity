# Point-infinity preliminary actual-print review

This is isolated candidate review, not repository snapshot generation or full
acceptance. Sources remain the archived, freshly compiled, independently
kernel-checked chain. No accepted snapshot or registry is changed.

## Standard isolated snapshot extension (2026-10-09)

All 71 new standard theorem records match the reviewed deep preliminary
prints modulo qualification and whitespace. All 22 definitions are accounted
for; 20 likewise match. The ordinary printer truncates fuel and generated
trace expressions with `...` in `point_write_run` and `point_write_tree`.
The separate deep prints have neither truncation, and exact source guards plus
the already kernel-checked run equality constrain those computed witnesses.
This is not a claim to have manually reviewed every trace node. Do not change
the ordinary snapshot printer or silently equate its truncated output with
the full terms. The supplementary normal-print interfaces are 1005 lines,
SHA-256 `50d2754a9105029c0164ac2194b31c5588397304f640ea6c1bf27f2670f1c13c`.

The final public type names the exact original `f_simplicity_gej_infinity`,
Unit input, left-associated triple Word256 output, and literal polymorphic
program specialized to CoreFunSem. There is no additional antecedent before
the common `secp_jet_local_spec`. The complete public-call type takes only
initial frame/base/alignment/capacity facts; helper execution, actual output
and freeing are conclusions derived inside its proof.

The lifecycle interface review confirms real source/point allocations and
Freeable ranges 16/128, freshness against the original memory, actual
`blocks_of_env` ordering, `Mem.free_list` success, copied frame storage and
outside-local framing. The owned public remainder derives its helper calls,
literal output and freeing permissions from initial ownership and finv.
Its helper adapter's call premises are discharged, not promoted to public
preconditions. No output-zero initialization or coordinate-value restriction
is added to the public theorem.

Printed literal zero and point definitions retain recursive zero at exponent
8 and left-associated pairing. Printed offsets are 0/40/80; field cells sit
inside one real 128-byte ownership region. Initializer/writer/public statement
definitions retain the exact generated field accesses and true return.

The expanded `point_write_tree` accounts for almost all of the 13 MB output.
It is a derived computational witness, not the canonical specification.
The actual source computes it from `point_write_run` separately for X/Y/Z;
the kernel-checked `point_write_run_eq` proves each equality to the real
symbolic run, and nonempty/storage/output-log lemmas constrain its use.
Review of those interfaces does not claim a manual exhaustive inspection of
every expanded trace node. All 71 helper/public interfaces were also inspected
in the supplementary normal-printer output `interfaces-readable.out` (1005
lines, compiler exit 0). This completes preliminary interface review, including
from-stores/from-calls adapters versus owned constructors, bounds, separation,
representation, field preservation, source copy and public cleanup. Standard
project snapshot extension comparison remains to be done before acceptance.

The archived inventories list 71 results and 22 definitions. They are assembly
inputs, not coverage: add only the complete public jet after correspondence,
snapshot review, isolated full acceptance and guarded checkout integration.
