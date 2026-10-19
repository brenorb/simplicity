# Actual original field-multiplication helper execution

`eval_field_mul_inner_owned_inplace` executes the unchanged original
`C.jets_secp.f_secp256k1_fe_mul_inner` in `secp_ge`. The output aliases the
first five-limb input, as in the public jet. The second owned five-limb input
is disjoint and preserved. Inputs are arbitrary `int64` limbs; representation
and outside-region memory framing are returned, and actual function entry,
calls, local allocations, return and frees are included.

This is **execution support only**. The five output symbolic expressions are
extracted from the real executor run, not assigned a mathematically correct
product. Their modular field value/ranges, the public reader/writer/lifecycle
and literal Simplicity specification bridge remain open. No jet coverage or
registration is added. RECKLESS configuration, production C and original
specifications are unchanged. Sources remain unregistered `.source` files.

The 52/64-bit shift dispatch composes separately proved original C helper
summaries. It introduces no assumed execution or libc premise. The other
internal helpers are executed by the existing verified executor.

Proof namespace: `/private/tmp/jet-secp-field-run.ZmrNBs` (`FieldRun`). It uses
the frozen source-bound tree `/private/tmp/jet-secp-shifts.SfCvHG`, including
the kernel-checked `SecpShift` extension (its pure numeric module is not loaded
by this execution-only root). The verifier rebuilds four additional unchanged
local imports explicitly, then recompiles both
new modules, inspects all 15 theorem types and 10 definitions, and checks
eleven closed results plus four with exactly the six inherited dependencies.
Every loaded local module must be one of the 15 previously forced imports or
one of the four freshly compiled imports. Main sources and staging are pinned.

The first strict loaded-closure gate stopped before acceptance: composing
the old 64-bit summary imports its oracle module, not only its already-bound
call/storage proof. That extra module is now freshly compiled explicitly;
the checked local closure is exactly 19 modules. The initial launch/failure
are preserved; no proof was changed to resolve this inventory issue.

`RUN.json` means compilation/reports succeeded; only `CHECKED.json` additionally
means recursive kernel verification succeeded. Launch files alone are not
success receipts. Preserve and poll a running handle instead of restarting it.

```sh
python3 -B proof-work/secp-field-mul-exec/verify.py kernel \
  /private/tmp/jet-secp-field-run.ZmrNBs
```

The initial output-reconstruction equality timed out at ten seconds with
both eager computation and direct conversion. The fix retains the same
conclusion: prove small region shape, definedness and untouched-input facts,
then apply `field_cells_rebuild`, a structural lemma which does not normalize
the large symbolic arithmetic expressions. No timeout was raised and no
required output fact was made an assumption.

Next: prove bounded integer observations for the actual five expressions,
show their base-`2^52` reconstruction equals the input product modulo
`2^256 - 2^32 - 977`, discharge the required bounds from actual `read_fe`,
and compose the original `fe_multiply`/`fe_multiply_beta` callers and their
literal specifications. `fe_square` has a separate original squaring routine;
do not silently replace it by this multiplication execution.

Reuse the existing `C.jet_secp_fe_math` definitions `feP`, `fe_val` and
`fe_limbs_ok`, its normalization/carry lemmas, and the existing uint128
multiply/accumulate numeric observations. The literal multiplication program
already exists as `canonical_fe_multiply` in `C.jet_secp_canonical_negate`,
with the 512-bit normalization bridge nearby. Verify those sources and their
dependency closure freshly when incorporating them; old objects or the
presence of an unregistered/untracked module are not admission evidence.
