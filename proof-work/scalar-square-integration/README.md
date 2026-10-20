# Normal square integration: reviewed preparation, not acceptance

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

Frozen preacceptance input:
`7522998e48f1441831821609af464ac2942a5424179077af9ea81ee0a1501176`.
Do not change candidate sources, manifests, scripts, registries, snapshots or
the linked production C/Haskell inputs while the full gate runs.

The earlier `--prepare-assumptions` mode already completed; do not rerun it.
These checks are read-only by default. The full acceptance command must rebuild,
check all registered modules/results/contracts/negative fixtures and compare
all four regenerated ASTs. Its terminal receipt, not this preparation, will
establish isolated acceptance. Source scope stays inherited local frames /
LP64 / RECKLESS; no new evaluator/all-frame/assertion-enabled/all-jet claim.
