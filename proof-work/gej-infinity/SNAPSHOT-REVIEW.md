# Point-infinity preliminary actual-print review

This is isolated candidate review, not repository snapshot generation or full
acceptance. Sources remain the archived, freshly compiled, independently
kernel-checked chain. No accepted snapshot or registry is changed.

Actual contract-print session **75319 passes with exit 0** using Coq 8.17.1,
the checked negation baseline and narrow `-R` overlay. Its script is
`/tmp/jet-gej-infinity.YrUC7w/infinity_contracts_review.v`; output is
`contracts-review.out` in that directory. It prints all 71 result types and
22 definitions with `Printing All`, width 120 and depth 10000. Output SHA-256:
`7645df1db9ac01165b66fc4b73a291d54e89cdd15ab79652472bb4cdb257dca4`.
No `(...)` truncation occurs. These deep-print settings do not replace the
project's standard snapshot printer or an actual snapshot diff review.

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
every expanded trace node. Other helper-type review and standard snapshot
extension comparison remain to be finished before full acceptance.

Actual assumption enumeration **18820 passes with exit 0**, log
`/tmp/jet-gej-infinity.YrUC7w/assumptions-review.out`. All 71 named records
were parsed and each set is a subset of the project's inherited allowlist.
The final public set is the six inherited assumptions: Classical choice and
excluded middle, dependent functional extensionality, and CompCert's two
parameterized external/inline-assembly semantics. No new name, assumed helper
execution/output/freeing fact or extra libc model is introduced. Exact parsed
records are preserved in `assumptions-provisional.expected.source`.

The archived inventories list 71 results and 22 definitions. They are assembly
inputs, not coverage: add only the complete public jet after correspondence,
snapshot review, isolated full acceptance and guarded checkout integration.
