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

Next: execute the original heads 50 through 67, through the first `r[0]`
store and following 52-bit shift. Keep the original cached input limbs
while updating the aliased output/input region; do not assume its old
memory contents survive that store.
