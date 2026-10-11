# Scalar multiplication: checked original-C helper closure

Three new modules / **17 completed results and 19 definitions** compile in
`/tmp/jet-scalar-mul.lkomWj` (`MulC`), against the unchanged frozen normal C
dependency tree `/tmp/jet-scalar-integration.XAMDsw/Coq`.
No main source, inventory, production C/Haskell or live audit input was edited.

The final freshly compiled theorem is
`MulC.jet_secp_u128_mul_exec.eval_u128_mul_owned_product`.
It proves the actual `jets_secp.f_secp256k1_u128_mul` call, return `Vundef`,
current loads of **both** product limbs, preserved owned representation and
outside-region memory framing. The underlying actual
`f_secp256k1_umul128` call returns the low limb and stores the high limb.
The input values are arbitrary int64s; initial output values are unrelated.
Storage contracts are owned 8-/16-byte regions, not arbitrary valid pointers.

The numeric bridge reuses the existing, checked
`C.jet_umul128_value.umul128_machine_observation` (already used for core
arithmetic jets). Small definitional equalities identify the new symbolic
execution's exact machine expressions with those existing observations.
No mathematical replacement of a public Simplicity specification was made.
The wrapper executes the real internal helper through a one-function table
whose actual symbol binding is proved; no oracle or call premise is assumed.

## Verification

- Builds: **26987**, direct chunk **099a36**, **80528**, all terminal exit 0.
- Independent kernel checks **41338** (underlying helper/numeric bridge) and
  **5111** (wrapper and dependency closure), both terminal exit 0. The
  inherited 15-axiom library context matches, all unsafe categories empty.
- `Print Assumptions` **77808**, terminal exit 0: 14 closed results, three
  execution results with exactly the six inherited Coq/CompCert dependencies
  recorded in `REVIEW.json`. No new assumption was introduced.
- The last contract command of **92276** terminated with exit 0: all 17
  types and 19 definitions printed at depth 100000, untruncated. Source,
  driver, output and kernel hashes are frozen and checked by `review.py`.
- `test-review.py`: thirteen in-memory dependency/contract/kernel mutations
  rejected, without editing proof inputs. Both reviewers exit 0.

Sources here are exact byte copies of the freshly compiled scratch files.
`manifest.json` and `REVIEW.json` pin their provenance and evidence.
This is **helper progress only**, not accepted/public scalar multiplication,
new registry coverage, arbitrary evaluator frames or assertion-enabled builds.
Main coverage remains 351/533. The separate scalar-add candidate remains
provisional until its full audit and main reconciliation are completed.

## Reproduce / continue

```sh
python3 -B proof-work/scalar-mul/review.py
python3 -B proof-work/scalar-mul/test-review.py
```

Compile from the dependency Coq directory, with the pinned compiler and
`ulimit -S -s 65520`:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_u128_mul_exec.v
bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC \
  MulC.jet_secp_u128_mul_exec
```

The actual `u128_accum_mul` allocation/call/cleanup and full modulo-128-bit
value observation are now checked in `../scalar-mul-accum` (11 further
results, nine closed); this archive and its 17-result evidence stay unchanged.
Next: original `scalar_mul_512` column/carry execution and product value;
then `scalar_reduce_512`. Reuse existing reader, generic Word256 writer,
owned public lifecycle, core product observations and literal-program
bridges. Prove exact helper summaries before using them to limit symbolic
expression growth; do not introduce assumed correct arithmetic, execution,
output, permissions or frees.

Keep the end-to-end roots in view: original public `scalar_multiply` and
`scalar_square` against their **literal canonical Simplicity programs**.
Neither is proved by this helper closure. No current failing Coq goal remains.
The initial helper compilation failed only because `repeat split` expanded
already-established representation/framing; `coqtop Show` exposed the
mismatch and explicit conjunction packaging fixed it, without new premises.

Parent full-audit **10545** now passed with terminal exit 0; preserve its
accepted candidate unchanged (do not restart it), and follow
`../scalar-add-integration/CONTINUATION.md` for acceptance/integration.
Claude owns Elements and the shared linkage/startup/constructibility work;
this archive is disjoint. Signed local atomic commits only; no pushes.
