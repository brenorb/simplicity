# Original field multiplier: composed execution through the second checkpoint

`exec_original_through_second` composes the first 32 original statement heads
with heads 32 through 49. Both source-splitting equalities are checked against
the unchanged `f_secp256k1_fe_mul_inner`. The second slice accumulates the
next five products and high-`p8` correction, shifts `d` by 52, and splits the
saved `t4` into its low 48 bits and `tx`.

The second slice's entry is **derived**, not an extra caller premise:
`first_atomic_regs_exact` identifies all four existing memory regions with
the typed entry, and `first_to_second_tmatch` establishes its live cached
inputs, pointers, constants and `t3`. No fresh buffers are allocated or
assumed at this boundary. Generic binding/value-transfer lemmas preserve the
actual live temporary relation without retaining large symbolic expressions.

The final theorem retains current loads of both `c`/`d` limbs, current
`t4`/`tx`, unchanged `t3`, atomic cell/temp representations and framing
outside the original footprint. It includes actual internal calls and their
allocation/free behavior. Machine arithmetic includes wrap; this packet
does not yet establish the second slice's unbounded integer/range bridge.

This is partial helper execution, not complete C-jet-to-Simplicity
equivalence. The original function-entry and reader/writer/lifecycle
obligations, later slices, final field-product bridge and public theorem
remain open. No production code, original specification, API, generation
configuration, main proof source or registry is changed. Coverage added: zero.

## Evidence

The five sources have 30 results and 27 definitions. The intended exact
profile is 28 closed results and two execution results with only the six
inherited Coq/CompCert dependencies. `RUN.json` records completed fresh
compilation/full contracts/assumptions; `CHECKED.json` additionally records
completed recursive kernel verification. A launch file is not success.

Audit tree: `/private/tmp/jet-field-checkpoint-audit.Zeze9g`, narrow namespace
`FieldSecond` in its separate `second/` directory. Its 95 local imports are
bound to the successful forced-source build and kernel check of
`../secp-field-checkpoint`. The pure parent `Columns` module is not loaded
by this execution-only root. All actually loaded modules are inventoried.

```sh
python3 -B proof-work/secp-field-second-exec/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

Next: derive exact second-fold integer values and carry bounds from the
first checkpoint and implementation limb bounds, then instantiate that
result on this composed C execution. The next slice is heads 50 through 67,
through the first `r[0]` store/52-bit shift. It writes into the first input
region: keep the **original cached input temporaries**, while updating the
output region representation. Do not recreate the original input contents
or assume a fresh output buffer when crossing that store.
