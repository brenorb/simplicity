# Checked compact execution and original scalar product helper

This theorem proves actual `jets_secp.f_secp256k1_scalar_mul_512` execution,
including allocation/free of its 16 product structs and the real internal
`u128_mul`, `umul128`, high-limb and low-limb calls. It returns `Vundef`,
initializes all eight output limbs, preserves both four-limb inputs and
owned representation, and frames memory outside the initial regions.
Inputs and previous output values are arbitrary int64s. The inherited
contract requires distinct owned 64-/32-/32-byte regions; it is not an
arbitrary-pointer/evaluator-frame theorem.

The full eight-limb product extension below now proves the integer product.
**Not yet proved:** `scalar_reduce_512`; original public scalar multiply/square
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

Reproduce read-only evidence checks:

From the dependency Coq directory, pinned Coq 8.17.1, CompCert 3.14, VST 2.14,
compiler PATH and `ulimit -S -s 65520`:

Continue with small column/carry value bridges, reusing the checked
`umul128_machine_observation` and wrapped-add carry lemmas rather than
unfolding the whole run into an open arithmetic goal. Prove exact C carrier
observations and bounds, compose the column invariants, then reduce modulo
the scalar order and connect the actual public caller to its literal program.
No source in these three completed files has a failing Coq goal.

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
This first-column checkpoint alone did not prove the remaining seven limbs
or full product. The extension below does; scalar reduction, public caller
lifecycle and literal canonical-program equivalences remain open.
Neither helper extension is a completed public jet equivalence.

For the next columns, retain `scalar_mul512_low_den` as a template: identify
the observed C machine expression by bounded conversion, then apply the
existing product/carry facts. Do not unfold `den` across the entire eight-word
array in an open goal. Maintain a radix-column invariant (including c2 bounds)
across the actual accumulation/extraction steps and compose its conclusion
with `eval_scalar_mul512_owned`.

## Checked full eight-limb product extension

Six additional modules / **50 results, 42 definitions** freshly compile;
49 results are closed, and the execution root has exactly the same six
inherited execution dependencies. Prior source/evidence archives stay
byte-identical. Last verified declaration:
`MulC.jet_secp_scalar_mul512_owned_product.eval_scalar_mul512_owned_product`.

It takes only `rep rho beta scalar_mul512_initial_regs m`, and proves the
actual original C function call, all eight `Mint64` loads in **final memory**,
their full unsigned 512-bit value equals the product of the two unsigned
256-bit inputs, final owned representation and outside framing. Previous
output values and both inputs are arbitrary. This retains the initial
distinct owned 64-/32-/32-byte region contract; it is not evaluator-wide or
assertion-enabled coverage and does not replace a public Simplicity spec.

Proof layering, reusable for reduction:

1. `machine`: exact C macro operations, low/high word and uint32 top carry.
2. `symbolic`: actual checked execution expressions match all eight machine
   outputs. Product binding, casts, carry, accumulation and extraction each
   have small representation lemmas. Avoid open whole-array `den` reduction.
3. `columns`: exact radix value through multiply-add; top no-wrap guard,
   extraction, and fast modulo/value lemmas.
4. `accumulate`: finite sums of products. At most four products per column
   and carried value below five words imply top carry safety; those guards
   are derived, not added to the call theorem.
5. `product`: follows the actual seven-column schedule and telescopes the
   first six emitted digits. Both input bounds imply the final residual
   fits two words, proving final fast-column exactness without a new premise.
6. `owned_product`: composes execution, exact expression representation,
   current-region loads and full product reconstruction.

Next: prove original `scalar_reduce_512` execution and its three fold stages
modulo the scalar order, reusing the column value lemmas and the checked
original scalar-reduce/overflow helpers. The actual function allocates 15
uint128 locals, reads eight limbs and calls u128 multiply/accumulate/shift/
projection helpers plus scalar overflow/reduce. Inspect that AST and build
small stage contracts; do not substitute an arithmetic reduction function
for its execution. Then compose the original public multiply/square caller
lifecycle with the existing canonical program/specification bridges.

That original reduce512 **execution** step now checks in `../scalar-reduce512`:
13 results / five definitions, actual helper calls/entry/free, preserved input,
and all four current output expression loads. The modulo-order value bridge
and public canonical roots remain open. Read its continuation before reusing
the product columns: reduction's top accumulator is **uint64**, not uint32.
