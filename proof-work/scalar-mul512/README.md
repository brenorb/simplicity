# Checked compact execution and original scalar product helper

Three modules / **19 completed results and 11 definitions** compile in
`/tmp/jet-scalar-mul.lkomWj` (`MulC`) against the immutable accepted normal C
candidate `/tmp/jet-scalar-integration.XAMDsw/Coq`.
Last verified declaration: `eval_scalar_mul512_owned` in
`MulC.jet_secp_scalar_mul512_run`.

This theorem proves actual `jets_secp.f_secp256k1_scalar_mul_512` execution,
including allocation/free of its 16 product structs and the real internal
`u128_mul`, `umul128`, high-limb and low-limb calls. It returns `Vundef`,
initializes all eight output limbs, preserves both four-limb inputs and
owned representation, and frames memory outside the initial regions.
Inputs and previous output values are arbitrary int64s. The inherited
contract requires distinct owned 64-/32-/32-byte regions; it is not an
arbitrary-pointer/evaluator-frame theorem.

**Not yet proved:** the combined eight-limb output equals the integer
product; `scalar_reduce_512`; original public scalar multiply/square
callers and their literal canonical Simplicity specification bridges.
The output expressions are defined from the checked execution, not assumed
correct. No public specification was substituted or coverage added.

## Fix the cause, not the timeout

The RECKLESS AST retains conditionals of shape
`Sifthenelse condition Sskip Sskip` inside single-pass macro loops.
The inherited symbolic executor creates an `RIf` even though both branches
leave the same state. Subsequent continuations are duplicated repeatedly.
The first full-tree experiment timed out at ten seconds. A projection asking
for a single normal leaf returned false: this does **not** establish that
execution returned `None`. Prefix probes exposed the retained branching;
the separate allocation probe compiled after importing `jet_sx_mem`.

`jet_sx_compact` solves this without changing the AST or canonical spec:

- It still evaluates the condition with `xexpr` and converts it with `xbool`;
  either failure still rejects the run.
- A Coq proof constructs the actual `exec_Sifthenelse` derivation for whichever
  Boolean is obtained. It does not assume the condition's value or discard
  its evaluability requirement.
- Sequences compose that rule; single-pass `Sloop body Sbreak` preserves
  normal, break, continue and return behavior. Other control flow and all
  internal helper calls use the existing verified executor.
- `compact_fun_pure` reuses verified function entry, allocation, actual calls,
  return conversion, freeing, representation and framing. Its generic helper
  premises are discharged in `eval_scalar_mul512_owned`.

Six closed regression proofs reject undefined/unconvertible conditions,
avoid forking a valid symbolic no-op condition, preserve loop returns and
continues, and retain branching when branch bodies have different effects.

Do not reify the original huge decision tree. Use bounded Boolean projections
and the compact run. The state is defined by a successful-run projection,
with independently proved completion, return, empty log and output shape.
No computed giant tree is an axiom or proof substitute.

## Verification

- Final executor build direct **0733e0**, scalar run build **73252**, checks
  direct **d00823**: all terminal exit 0. Each speculative tactic bounded
  at ten seconds, compilations with process deadlines.
- Independent kernel **82108** checks executor/product roots and closure;
  **92056** checks regression root. Both terminal exit 0. Main closure matches
  the inherited 15-axiom context; the regression-only closure is its pinned
  12-axiom subset. All three unsafe categories are empty.
- Fail-fast drivers **2774**, terminal exit 0: all 19 exact dependencies
  (16 closed, three with the same six inherited execution dependencies), all
  19 types / 11 definitions printed untruncated at depth 100000; no diagnostics.
- `manifest.json` and `REVIEW.json` pin exact source/driver/output/kernel
  evidence. `review.py` revalidates the dependency fingerprint and prior
  checked product archive; `test-review.py` rejects eleven in-memory
  contract/status/dependency mutations. No live audit input was changed.

Reproduce read-only evidence checks:

```sh
python3 -B proof-work/scalar-mul512/review.py
python3 -B proof-work/scalar-mul512/test-review.py
```

From the dependency Coq directory, pinned Coq 8.17.1, CompCert 3.14, VST 2.14,
compiler PATH and `ulimit -S -s 65520`:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_scalar_mul512_run.v
bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC \
  MulC.jet_sx_compact MulC.jet_secp_scalar_mul512_run
```

Continue with small column/carry value bridges, reusing the checked
`umul128_machine_observation` and wrapped-add carry lemmas rather than
unfolding the whole run into an open arithmetic goal. Prove exact C carrier
observations and bounds, compose the column invariants, then reduce modulo
the scalar order and connect the actual public caller to its literal program.
No source in these three completed files has a failing Coq goal.

Main coverage remains 351/533; isolated scalar-add 359/533 remains provisional
while its full audit **38737** runs (now past kernel, at assumption gate).
Follow `../scalar-add-integration/CONTINUATION.md`; do not restart/mutate it.
Claude owns Elements and shared obligations; no overlap, registries untouched.
All-533 goal active and unfinished; local signed atomic commits, no pushes.

## Checked first-column value extension

The original three-module / 19-result evidence above stays byte-identical.
`jet_secp_scalar_mul512_low.v.source` adds **six results / two definitions**;
last verified theorem `eval_scalar_mul512_owned_low_product` includes the
actual original call and a **current-memory** `Mint64` load at output offset
zero equal to the product of both full 256-bit C input values modulo 2^64.
It takes only the original owned input representation, retains all final
representation and framing, and imposes no arithmetic/helper/output premise.

The low-word machine bridge reuses
`MulC.jet_secp_umul128_numeric.umul128_unsigned_outputs` rather than reproving
the multiplication algorithm. A small internal modular identity connects the
first limb to the four-limb C value. This is not a public Simplicity spec.
The remaining seven output limbs, full product identity, scalar reduction,
public caller lifecycle and literal canonical-program equivalences remain
open. This extension does not make `scalar_mul512` a completed public jet.

Verification: final build direct **71d1db**, independent kernel **50870**,
fail-fast assumption/contract drivers **33364**, all terminal exit 0. Five
results are closed; the execution root has exactly the same six inherited
dependencies. Complete six types/two definitions print without ellipses or
diagnostics; the inherited 15-axiom kernel context matches, unsafe categories
are empty. Exact evidence is in `LOW-REVIEW.json`; replay the read-only check:

```sh
python3 -B proof-work/scalar-mul512/review-low.py
```

For the next columns, retain `scalar_mul512_low_den` as a template: identify
the observed C machine expression by bounded conversion, then apply the
existing product/carry facts. Do not unfold `den` across the entire eight-word
array in an open goal. Maintain a radix-column invariant (including c2 bounds)
across the actual accumulation/extraction steps and compose its conclusion
with `eval_scalar_mul512_owned`.
