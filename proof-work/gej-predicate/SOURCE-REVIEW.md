# Supplemental predicate source correspondence

The archived gate and mutation test both passed with terminal exit 0 against
the repository sources and exact materialized predicate/infinity candidates.
The gate uses the existing nested-comment-aware Haskell/Coq parser, exact
active program/definition/public statement comparisons, and scoped C function
and registration checks. It has no update mode and does not change snapshots.

Checked bindings:

- CoreJets `GejIsInfinity` GEJ-to-Bit type, canonical specification and FFI.
- Canonical record `gej_is_infinity = drop fe_is_zero`, literal Coq drop port
  and complete existing `secp_jet_local_spec` statement.
- Original public C read/accessor/bit-write/true return, all three original
  coordinate reads and Z zero-test, and the original flag accessor.
- Actual 16/128 allocations, generated undefined initial temporaries, shared
  local ranges/free_list and derived entry/setup/rest/free proof bindings.
- Bitcoin and Elements jet/source/target registration fields.

All **37** in-memory mutations were rejected: wrong catalogue/spec/FFI,
canonical or literal projection, numeric replacement, allocation size,
temporaries, lifecycle/free binding, added false premise, narrowed input or
wrong result type, skipped/duplicated coordinate reads, wrong zero-test
coordinate/accessor, constant bit/false return, and registration changes.

These finite text checks are supplemental, not an exhaustive semantic audit,
Haskell compiler, transitive fidelity certificate, cryptographic CMR proof,
evaluator-admissibility proof, or replacement for full acceptance. Inherited
canonical field-zero ports still require their existing correspondence gate.
The 62 formal results retain their independent public kernel evidence; no
new registered coverage or full acceptance is claimed here.

Reproduce after materializing the exact archived sources (Python 3):

```sh
python3 /tmp/jet-gej-predicate.W2FtCz/check-gej-predicate-wiring.py \
  --repo /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity \
  --candidates /tmp/jet-gej-predicate.W2FtCz \
  --dependencies /tmp/jet-gej-infinity.YrUC7w
python3 /tmp/jet-gej-predicate.W2FtCz/test-gej-predicate-wiring.py \
  --repo /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity \
  --candidates /tmp/jet-gej-predicate.W2FtCz \
  --dependencies /tmp/jet-gej-infinity.YrUC7w
```

For a future isolated integration, candidates and dependencies can both be
its Coq/C directory. Wire this gate/test into that isolated acceptance target;
do not edit the currently live checkout audit inputs to add them.
