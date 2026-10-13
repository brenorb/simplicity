# Normal square integration: reviewed preparation, not acceptance

The complete public square proof and its exact selected closure now build in
the normal `C` namespace at `/tmp/jet-scalar-square-integration.MAhL2g/Coq`.
Parent: immutable accepted multiply candidate
`/tmp/jet-scalar-multiply-integration.yIS07H/Coq` (360/533).
Main's dirty sources, staging and registries are untouched.

`ASSEMBLY.json` pins **15 new modules, 47 results and 18 definitions** from the
three checked square archives. Only namespace references are changed. There
are no excluded/unselected modules in this closure, and all old proof sources
and inherited infrastructure stay identical except exact registry/gate
extensions and separately reviewed snapshots. Only one public jet is selected:
`simplicity_scalar_square` ->
`C.jet_secp_scalar_square_local.scalar_square_literal_local_spec`.
The literal target and parametric adapter are retained.

## Terminal preparation checks

- Normal build **79279**, exit 0: all 15 new modules freshly compiled.
- New assumptions **32019**, exit 0: all 47 exact scratch counterpart sets
  match; 28 closed results.
- Deep contracts **28600**, exit 0: 75,320 bytes, untruncated.
- Contract generation **51561**, exit 0: preparation only, not acceptance.
- Independent root/whole-dependency kernel **68228**, exit 0: inherited
  15-axiom context matches; all three unsafe categories empty.
- Full normal review **82901**, exit 0: 7,234 inherited contract records are
  byte-identical/in order; all 4,767 inherited dependency records unchanged.
- Eleven in-memory normal-review corruption tests and eight public-boundary
  mutations passed. Coverage/static tests and production/canonical source
  identity (240 files) passed.

The compact printer elides one internal run definition; the full report checks
every fragment against its untruncated counterpart. No type/definition check
is omitted. Existing ordered-record handling retains duplicate names and the
three explicit inherited constructor/parent Print aliases, not generic aliases.
The assumption snapshot is installed only as the exact reconciled extension
through `apply_patch`; generation/review does not accept it.

`PREPARATION.json` pins terminal evidence. Provisional coverage is **361/533**
(257 entries without an extra library premise, 104 explicitly conditional on
`memcpy_model`). This is **not accepted coverage** until complete
`check-jets.sh --accept` passes without update/no-build flags. Main remains
separate at 351/533 at the last exact comparison.

The complete acceptance gate has been launched and verified live as session
**41316**. `AUDIT-RUN.json` is a launch record, not terminal success. Poll that
same handle and keep its inputs frozen; do not restart on observation timeout.

Frozen preacceptance input:
`7522998e48f1441831821609af464ac2942a5424179077af9ea81ee0a1501176`.
Do not change candidate sources, manifests, scripts, registries, snapshots or
the linked production C/Haskell inputs while the full gate runs.

```sh
python3 -B proof-work/scalar-square-integration/review-normal.py --assembly proof-work/scalar-square-integration/ASSEMBLY.json
python3 -B proof-work/scalar-square-integration/test-review.py
python3 -B proof-work/scalar-square-integration/test-square-public.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-square-integration.MAhL2g/Coq
```

The earlier `--prepare-assumptions` mode already completed; do not rerun it.
These checks are read-only by default. The full acceptance command must rebuild,
check all registered modules/results/contracts/negative fixtures and compare
all four regenerated ASTs. Its terminal receipt, not this preparation, will
establish isolated acceptance. Source scope stays inherited local frames /
LP64 / RECKLESS; no new evaluator/all-frame/assertion-enabled/all-jet claim.

See `CONTINUATION.md`. Keep the all-533 goal active; respect Claude's shared/
Elements reservation and existing main staging. Signed local commits only;
never push.
