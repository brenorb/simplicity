# Original field multiplier: second checkpoint integer bridge

`exec_original_second_integer_atomic` attaches exact integer values and
range bounds to the execution of the first 50 statement heads of the
unchanged `f_secp256k1_fe_mul_inner`. It reuses the checked composed C
execution, including its derived intermediate memory/temporary relation,
internal calls, allocation/free behavior and outside-footprint framing.

Under the implementation limb bounds (`field_input_bounds`), the second
accumulation is an exact unbounded integer sum: its intermediate two-limb
additions do not overflow. After shifting by 52, `d` is below `2^64`.
The saved remainder is split exactly into `tx < 16` and `t4 < 2^48`.
These values and ranges are derived, not assumed as extra execution
premises. `Accum.v.source` factors a reusable bounded machine-accumulation
lemma for subsequent checkpoints.

This is still partial helper execution, not a complete jet equivalence.
The caller must still establish the limb bounds; remaining multiplication
stages, final field-product bridge, original function entry and jet
reader/writer/lifecycle composition remain open. No production C, original
specification, API, generation setting, main proof source or registry is
changed. Coverage added: zero.

## Evidence

The two sources have 25 results and 10 definitions. The exact intended
assumption profile is 24 closed results and one execution theorem with
the six inherited Coq/CompCert dependencies. `RUN.json` records fresh
compilation and full type/definition/assumption reports; `CHECKED.json`
additionally records completed recursive kernel verification. A launch
file alone is not a successful check.

The audit tree is `/private/tmp/jet-field-checkpoint-audit.Zeze9g`, with
the new sources in `second-values/` under namespace `FieldSecondValues`.
The two checked parents bind the same 95 forcibly rebuilt local imports,
11 shared execution-support modules, five second-slice execution modules
and the first-checkpoint integer module. All loaded modules are inventoried
and their exact source/object hashes checked before and after verification.

```sh
python3 -B proof-work/secp-field-second-values/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-second-values/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

Next: execute the original heads 50 through 67, through the first `r[0]`
store and following 52-bit shift. Keep the original cached input limbs
while updating the aliased output/input region; do not assume its old
memory contents survive that store.
