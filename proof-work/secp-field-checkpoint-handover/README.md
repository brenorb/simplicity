# Reusable original field checkpoint after output stores

`checkpoint_regs` distinguishes the array currently in memory (`written`)
from the original cached input limbs (`digits`). Its fixed four-region
layout retains the existing arrays, `c` and `d`, with the same ownership
and shape. `checkpoint_temps` keeps the original cached inputs and live
`t3`/`t4`. These are representation changes, not new physical buffers.

`third_atomic_regs_exact` and `third_to_checkpoint_tmatch` derive this
layout from the actual post-store third-slice state. In particular, the
first slot contains the new `r[0]`, while cached `a0` still contains the
original input. `exec_original_third_checkpoint` composes these facts
with original C execution through 68 statement heads, retaining current
observations and framing outside the original footprint. It assumes no
fresh memory, previous input load, or intermediate correctness result.

This is reusable support, not a complete new jet equivalence; coverage
added is zero. Production C, original specifications, API, generation
configuration, main proof sources and registries are unchanged. Remaining
multiplier stages, final field-product bridge and public jet composition
are still required.

Next: instantiate `checkpoint_state` for the original slice ending with
`r[1]`, update `written` after that store, and keep `digits` fixed. Use the
derived handover theorem to discharge that slice's entry relation. Continue
reusing `accumulate_exact`, `products56_bound`, and the existing shift/mask
value lemmas for the subsequent arithmetic bridges.
