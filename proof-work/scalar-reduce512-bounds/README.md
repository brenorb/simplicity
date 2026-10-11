# Sharp fold bounds and checked actual second prefix

Two modules / **14 closed results, 12 definitions** freshly compile in `MulC`
against `/tmp/jet-scalar-integration.XAMDsw/Coq`, scratch
`/tmp/jet-scalar-mul.lkomWj`. They reuse the frozen checked first fold in
`../scalar-reduce512-first` and do not change any public registry.

`jet_secp_reduce512_fold_bounds` proves the exact C constant identity
`D = 2^256 - canonical_group_order`, D^2 < 2*2^256, and the sharper first-fold
high256 <= D bound. The first fold preserves the full original input modulo
the canonical order. Its second-fold **integer bridge expression** has value
below 3*2^256 and preserves that residue. This is an internal bridge, not a
replacement specification or a claim that the second C fold already emits it.

`jet_secp_reduce512_second_run` cuts the actual unchanged generated body after
`_p4`, proves exact source reconstruction and the cut boundary, and checks
completion of the actual compact run. All five output temps are present and
their zero-extended expression carriers are Vlong-kind. It uses the real
15-local allocation and already proved shift64 helper table. No new prefix
big-step execution theorem is asserted.

**Remaining:** bind all five actual second-fold expressions to the machine
schedule; derive fast-operation guards; reconstruct their numeric value;
prove the real p4 narrowing lossless and <= 2; then prove third/final reduction,
compose the whole helper's current-memory output loads, and finish public
multiply/square lifecycle and literal canonical Simplicity bridges.

## Checks and reuse

`REVIEW.json` records the fresh terminal build/driver/kernel checks and exact
hashes. All 14 results are closed under the global context; inherited kernel
axioms match the same 15-item context and unsafe categories are empty.
Full-depth types and definitions are untruncated; stderr is empty. Read-only
review revalidates the frozen first-fold/execution/product prerequisites and
source fingerprint. Negative fixtures mutate evidence in memory only.

```sh
python3 -B proof-work/scalar-reduce512-bounds/review.py
python3 -B proof-work/scalar-reduce512-bounds/test-review.py
```

LP64 / RECKLESS remains the target. No arbitrary evaluator-frame,
assertion-enabled, public-coverage or full-acceptance claim is added.
See `CONTINUATION.md` for the exact unfinished source binding. Keep verified
sources and audit inputs frozen and preserve unrelated main-checkout changes.
