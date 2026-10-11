# Checked source-bound first fold of scalar_reduce_512

Six fresh modules, **49 closed results / 71 definitions**, including record
constructors and projections, build against the immutable accepted dependency
tree `/tmp/jet-scalar-integration.XAMDsw/Coq`. Scratch namespace `MulC` lives
at `/tmp/jet-scalar-mul.lkomWj`. The last verified declaration is
`MulC.jet_secp_reduce512_first_value.reduce512_first_source_value`.

This proves that the seven emitted first-fold limbs have exact value
`low256(input) + high256(input) * (C0 + 2^64*C1 + 2^128)` for arbitrary
eight-limb machine inputs. The real narrowing into uint32 `m6` is included:
the untruncated carry is proved at most one, and the cast loses no bits.
No carry-safety premise is added at the final first-fold value boundary.

## Connection to the implementation

- `first_run` cuts the **actual unchanged generated body** immediately after
  the assignment to `_m6`. It proves exact source reconstruction and the cut
  boundary, then checks completion of the compact executor with the actual
  15-local allocation, parameters, input/output representation and proved
  shift64 helper table. The prefix uses actual source, not a new C function.
- `first_symbolic` proves by conversion that this run's seven expressions
  equal the factored macro schedule. Its denotation is the exact machine
  schedule, including the 32-bit cast.
- `wide` and `symbolic` account for the **uint64 top** of reduce512 and actual
  signed/unsigned promotion casts. The product helper's uint32-top model
  cannot substitute for this model unchanged.
- `accumulate` derives no-wrap guards for the finite mixed multiply/sum lists.
  `first_value` reconstructs the exact multi-limb value, deriving every fast
  operation's guard and the narrowing bound from machine input ranges.

This archive does **not** add a prefix big-step theorem or compose the new
value result with the full helper call. The complete unchanged helper's
allocation/free, calls, current-memory loads and frame preservation were
independently checked in `../scalar-reduce512`. That execution evidence is
revalidated as a prerequisite, not replaced or weakened here. LP64 / RECKLESS
remains the target; arbitrary evaluator frames and assertion-enabled builds
are not newly established.

Second/third-fold value bridges, the full modulo-order output identity, actual
public multiply/square lifecycles and literal canonical Simplicity bridges
remain open. There is **no public coverage increase or full acceptance**.

## Verification

Fresh fail-fast build **93994**, independent kernel check **67918**, and full
type/definition/assumption drivers **22400** all exited zero. All 49 results
are closed under the global context. The kernel closure has the same 15
inherited context axioms; unsafe categories are empty. Full-depth drivers
print every type and definition without truncation and have empty stderr.
`manifest.json` and `REVIEW.json` pin exact source/driver/output/kernel hashes.
Read-only review also checks the frozen product/execution prerequisites and
their dependency fingerprint. Nine in-memory negative fixtures pass.

```sh
python3 -B proof-work/scalar-reduce512-first/review.py
python3 -B proof-work/scalar-reduce512-first/test-review.py
```

From the dependency Coq directory, pinned Coq 8.17.1 on PATH, stack 65520 KiB:

```sh
bash build-jets.sh --coqc -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_reduce512_first_value.v
bash build-jets.sh --coqchk -silent -o -R /tmp/jet-scalar-mul.lkomWj MulC \
  MulC.jet_secp_reduce512_first_value
```

All checks are terminal. No failing goal remains in the six archived modules.
Keep their exact sources/evidence frozen; continue in new modules. See
`CONTINUATION.md`. Preserve the main checkout's unrelated dirty work and
Claude's Elements/shared-obligation reservation. Signed local commits only.
