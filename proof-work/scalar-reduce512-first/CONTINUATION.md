# Continue the remaining actual scalar reduction stages

Last checked: `reduce512_first_source_value`, all 49 new results closed,
fresh build/kernel/drivers and negative evidence checks terminal zero.
No current failing Coq goal. Do not redo the full helper's execution or the
first fold; compose them with the remaining stages.

## Checked reusable interfaces

The immutable `MulC.jet_secp_reduce512_*` modules in this archive provide:

- `wide_muladd_value`, `wide_sumadd_value`: exact full-column updates under
  a top-field no-wrap guard. Fast variants require zero top and total < M^2.
- `wide_extract_decomposition` / `wide_extract_value`: radix decomposition
  and quotient. Fast extraction needs zero top.
- `wide_accumulate_small`: a list of at most four multiply/sum operations
  starting below 5M gives exact accumulation and extracted carry below 5M.
- `wide_*_rep`: exact symbolic-to-machine operations with the actual casts.
- `first_outputs_machine`: all seven source-derived first-fold expressions
  denote their machine words, including `m6` narrowing.
- `first_machine_value`, `first_m6_bound`, `first_m6_cast_exact`: exact fold
  value, carry <= 1, and lossless cast for arbitrary original machine inputs.

`reduce512_first_source_value` uses `il` on source expressions; the separate
`first_outputs_machine` equality proves these are Vlong values, so decoding
does not silently discard a carrier-kind obligation.

## Next finite source stages

1. Prove the checked constants' identity `D = 2^256 - canonical_order`;
   `first_delta` is currently the exact C constant expression, not an assumed
   canonical-order identity. Derive first-fold high256 <= D from its value.
2. Extract the actual prefix ending at `_p4`, using the existing spine cut.
   Prove its source reconstruction, run completion and emitted temp kinds.
   Bind the second-fold expressions to the exact macro schedule, including
   the real unsigned cast of `m6` and narrowing into `p4`.
3. Reuse wide-operation representations, finite accumulation and telescoping
   to prove the second fold's value. Its last phase is three fast operations:
   sum `m3`, multiply `m6*C1`, sum `m5`. Derive each guard, and account for
   the final `p4 = c0 + m6` (not just `p4 = c0`).
4. Use exact D to show D^2 < 2*2^256, hence second < 3*2^256 and p4 <= 2.
   A loose D < 2^129 bound is insufficient for this sharp bound. The current
   first-fold bound suffices for m6 <= 1 but does not itself prove high <= D.
5. Bind the actual third-fold u128 operations and current output loads. With
   p4 <= 2, prove their pre-final value < 2*order and c <= 1. If c=1 the
   wrapped low part is below order, so check_overflow is zero. Reuse the
   accepted overflow/final scalar_reduce arithmetic and execution results.
6. Compose the stages with `eval_scalar_reduce512_owned_loads`; each fold
   preserves modulo order because 2^256 = order+D. Then compose the original
   product/helper calls, public writer and cleanup, and literal Simplicity
   multiply/square programs. Integer arithmetic alone earns no public entry.

Authoritative unchanged C: `C/secp256k1/scalar_4x64_impl.h` lines 513 onward;
AST: `Coq/C/jets_secp.v` original `f_secp256k1_scalar_reduce_512`.

## Diagnosed pitfalls

Import `MulC.jet_secp_scalar_mul512_machine` explicitly when using its column
operations; consumer imports do not necessarily export those identifiers.
`change (... = _) in H` cannot infer arbitrary RHS placeholders: use the
exact equality. This CompCert has no `Int64.loword_unsigned` lemma; unfold
`Int64.loword`, then rewrite `Int.unsigned_repr` with the derived range and
finish with `Int64.repr_unsigned`. Keep fast no-wrap guards explicit inside
helpers and derive them at the end-to-end boundary. Bound speculative tactics
at ten seconds; inspect actual failures rather than extending timeouts.

Main coverage is still 351/533; isolated scalar-add acceptance is 359/533.
Its exact main reconciliation remains a separate pending step in
`../scalar-add-integration/CONTINUATION.md`. No new registry edits here.
