# Original multiply-accumulate: checked helper extension

Two modules / **11 completed results and eight definitions** compile in
`/tmp/jet-scalar-mul.lkomWj` (`MulC`). The dependency base is the immutable
accepted normal C candidate `/tmp/jet-scalar-integration.XAMDsw/Coq`.
The prior 17-result unsigned multiplication closure remains byte-identical
and is revalidated by this archive's reviewer.

Last verified declaration:
`MulC.jet_secp_u128_accum_mul_numeric.eval_u128_accum_mul_owned_product`.
There is no remaining failing Coq goal in these two files.

The theorem derives the **actual original**
`jets_secp.f_secp256k1_u128_accum_mul` call, `Vundef` return, both current
output loads, owned 16-byte representation and outside-region framing.
Clight execution includes real allocation/freeing of the local high-word
slot and the actual internal `umul128` call. No execution, output, store,
permission or successful-free fact is a new premise.

The combined output value is
`(old_hi * 2^64 + old_lo + unsigned_a * unsigned_b) mod 2^128` for arbitrary
int64 operands and initial accumulator limbs. No no-overflow premise is
imposed. The numeric observation reuses the checked multiplication and
wrapped-add carry lemmas. The small two-limb recombination identity is an
internal bridge to this executed C algorithm, not a replacement public spec.

## Evidence

- Exec build **58521**, terminal exit 0; numeric build direct chunk **d0a20a**,
  terminal exit 0. Each speculative tactic was bounded at ten seconds.
- Independent kernel **21794**, terminal exit 0, checking both new roots and
  their closure: inherited 15-axiom context matches, unsafe categories empty.
- Fail-fast driver run **95639**, terminal exit 0: exact 11-result dependencies
  (nine closed; two execution results have the same six inherited assumptions),
  all 11 types/eight definitions at depth 100000, no ellipses or diagnostics.
- Pinned source/driver/output/kernel hashes and parent receipts match.
  `review.py` and both this and the underlying archive's mutation tests exit 0.
  Seven new contract/status fixtures and thirteen inherited evidence fixtures
  reject drift in memory, without changing live audit inputs.

The first numeric attempt failed because a local product alias obscured the
two sides under division; `coqtop Show` exposed it and unfolding that alias
plus associativity closed the goal. A separate `mod_unique` orientation
mismatch was diagnosed from its printed goal. Neither fix changed statements
or added assumptions. Preserve these exact completed sources, not the failed
prefixes or stale compiled files.

## Reproduce / next

```sh
python3 -B proof-work/scalar-mul-accum/review.py
python3 -B proof-work/scalar-mul-accum/test-review.py
```

From the dependency Coq directory, pinned Coq 8.17.1 / CompCert 3.14 / VST
2.14, compiler PATH and `ulimit -S -s 65520`:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_u128_accum_mul_numeric.v
bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC \
  MulC.jet_secp_u128_accum_mul_exec MulC.jet_secp_u128_accum_mul_numeric
```

Next is original `scalar_mul_512` column/carry execution and product value,
then `scalar_reduce_512`, then the original public scalar multiply/square
callers against literal canonical Simplicity programs. Measure any closed
symbolic-run experiment with a short bound; do not assume an inlined large
tree will be manageable. Factor exact, proved helper summaries when needed.
Reuse actual reader/writer/owned lifecycle interfaces; all public call,
output, cleanup and canonical-spec obligations still require discharge.

This is **helper progress**, not public scalar equivalence, accepted coverage,
all evaluator frames or assertion-enabled execution. Main remains 351/533;
full scalar-add audit **38737** is live and must not be restarted or mutated.
Claude owns Elements/shared obligations. Signed local atomic commits only;
no production C/Haskell changes or pushes.
