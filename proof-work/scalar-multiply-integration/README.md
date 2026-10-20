# Normal scalar-multiply integration candidate

## Full acceptance completed

Seven new internal u128 definition names coincide with old core definitions.
The contract driver loads `C.jet_secp_umul128_exec` without opening it, while
checking/printing all its qualified names. This preserves inherited printing
context and omits no checks. Coq also prints the entire parent declaration
for constructors `wcolumn`, `Wmul` and `Wsum`. The snapshot parser handles
exactly these three checked cases, preserving ordered duplicate records and
requiring the constructor in the parent print. It does not relax arbitrary
declaration mismatches. Eleven in-memory corruption fixtures test the parser;
five more reject weakened/wrong public boundary contracts.

These are read-only preparation checks. Only the separate complete acceptance
run can accept the reviewed snapshots and four regenerated ASTs. The earlier
`--update` contract-generation operation prepared a candidate snapshot;
it was not acceptance. Assumptions were prepared by exact checked extension,
and the full acceptance command uses no update/no-build flags.
