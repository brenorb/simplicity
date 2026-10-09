# Point-infinity preliminary actual-print review

This is isolated candidate review, not repository snapshot generation or full
acceptance. Sources remain the archived, freshly compiled, independently
kernel-checked chain. No accepted snapshot or registry is changed.

## Standard isolated snapshot extension (2026-10-09)

Exact-source candidate build **9386 passes with exit 0**, log
`/tmp/jet-infinity-accept.xBQOUj/build-exact.log`. Standard contract generation
**48412 passes with exit 0**, log `contracts-update.log` in that root.
The actual standard snapshot adds 1322 type lines and 4159 definition lines,
with no deletion or replacement: all 140783 baseline lines remain verbatim
and in order. Candidate snapshot SHA-256:
`814446b2c4a231982e419859005ad79719d648e079ca1a437e8487a3bb8d454b`.

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

Standard assumptions **70735** are still running; log
`assumptions-update.log`. The read-only `review-snapshots.py` compares exact
baseline preservation, all added interfaces/definitions, proof source guards
and every assumption record. Run it only after 70735 finishes with exit 0.
Full acceptance and guarded checkout integration remain open.

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
every expanded trace node. All 71 helper/public interfaces were also inspected
in the supplementary normal-printer output `interfaces-readable.out` (1005
lines, compiler exit 0). This completes preliminary interface review, including
from-stores/from-calls adapters versus owned constructors, bounds, separation,
representation, field preservation, source copy and public cleanup. Standard
project snapshot extension comparison remains to be done before acceptance.

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
