# Original field multiplier: through the third output store

`exec_original_fifth_integer_checkpoint` executes the first 97 original
statement heads of `f_secp256k1_fe_mul_inner`, through `r[2]` and the following
52-bit `c` shift. Its slice boundary was inspected in the normalized Clight
statement tree; source-splitting equalities are checked against the unchanged
function body. The preceding `d` shift is by **64**, not 52 bits.

Entry comes from the actual post-`r[1]` checkpoint. The new current-memory
output load is established alongside preservation of `r[0]` and `r[1]`.
The proof returns an updated reusable checkpoint, preserving original cached
input limbs, live temporaries and framing outside the original footprint.
It does not assume a fresh array or reuse old loads after stores.

The arithmetic bridge reuses bounded accumulation for the three low-column
and two high-column products. `pair_low_mod64` connects the current low word
to the unbounded value modulo `2^64`; the existing 64-bit shift theorem
establishes its quotient. Intermediate sums fit in 128 bits under the
implementation limb bounds. The shifted `c` is below `2^63`, shifted `d`
below `2^50`, and stored `r[2]` below `2^52`. Exact values and bounds are
derived, not extra execution premises.

## Evidence and scope

Four sources, 41 results and 37 definitions. The expected exact dependency
profile is 36 closed results, two representation/load lemmas with four
inherited classical dependencies, and three execution results with the six
inherited Coq/CompCert dependencies. `RUN.json` records fresh compilation and
full type/definition/assumption reports. `CHECKED.json` additionally records
completed recursive kernel verification; a launch file is not success.

The first audit compiled the proofs and checked their exact assumption
profile, but rejected the loaded closure: its copied namespace filter had
omitted `FieldFourth`. `verify-initial-closure.py.source`, the original
`LAUNCH.json`, and `initial-closure-assumptions.log` retain that failed audit.
The corrected checker inventories **every** non-standard module and rejects
any module lacking exact source/object provenance. `RECHECK-LAUNCH.json`
starts the corrected run. No proof or dependency was changed for this repair.

Audit tree: `/private/tmp/jet-field-checkpoint-audit.Zeze9g`, new sources in
`fifth/` under `FieldFifth`. The parent binds the 95 previously forcibly
rebuilt local imports and 30 checked extension modules. Every loaded module's
source/object provenance is checked before and after verification.

```sh
python3 -B proof-work/secp-field-fifth/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-fifth/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

This remains partial helper execution, not complete jet equivalence; coverage
added is zero. Remaining final reduction/output stores, field-product bridge,
function entry and public reader/writer/lifecycle composition remain open.
The caller must still establish the implementation limb bounds. No production
C, original specification, API, generation setting, main proof source or
registry is changed.

Next: use the returned checkpoint for the final original slice, beginning at
head 97. The inspected spine has 107 heads, followed by `mul_last`. Its
remaining operations include `c += (R << 12) * low(d)`, `c += t3`, the `r[3]`
store and shift, and the final `r[4]` addition. Prove that word accumulation
and last addition fit their carriers; do not silently identify machine sums
with unbounded sums. Compose with `after_fifth`, retaining all earlier output
loads and the real function's local-allocation/free obligations.
