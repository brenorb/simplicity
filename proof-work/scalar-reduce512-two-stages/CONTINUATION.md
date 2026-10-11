# Continue with the actual third and final scalar reduction stages

Superseded continuation: the actual third-stage source/value/execution and
its internally discharged checkpoint are now checked in
`../scalar-reduce512-three-stages/`. Follow that archive's `CONTINUATION.md`
for the final reduction and full function/public boundaries. This pointer
does not change these frozen Coq sources or verification receipts.

Last verified: `exec_reduce512_first_two_stages`. All eight archived sources
compile completely; kernel, type/definition/assumption and evidence checks are
recorded in `REVIEW.json`. No failing goal remains in these files.

The old monolithic `jet_secp_reduce512_second_symbolic.v` experiment remains
uncompiled and is **superseded**, not a required next step. Do not restart its
whole-array/p3 conversion. The typed stage proves all five source expressions
and real execution; the composition root discharges the checkpoint from the
actual first prefix. The temporary fresh-XLv stage experiments are also not the
archived implementation; keep the original valuation and typed XL/XI leaves.

## Reuse the verified checkpoint pattern

1. Cut the actual statement spine at a checked boundary. Parameterize only
   the required machine-valued temps, using `XL` for Vlong and `XI` for Vint.
   These retain carrier kinds; `XV (Vlong x)` would have kind KV and is unsuitable.
2. Keep original rho, layout, concrete memory and concrete temp environment.
   Derive the one-way `tmatch` for a small checkpoint. Dead symbolic temps can
   be omitted; every temp read before overwrite must be supplied, including
   pointer parameters. `tmatch_checkpoint_set` changes symbolic temps without
   mutating the concrete environment.
3. Keep real initialized output/input cell loads. Forget only scratch-local
   values with `rep_forget_after`, retaining all permissions/ownership/shape.
   Metadata equality alone does not prove representation. The second stage's
   initial representation follows from the actual first postcondition and
   checked `reduce512_first_forget_stack`.
4. Use `compact_stmt_shift64_normal` to derive actual execution with the
   already-proved original shift64 helper table. The generic theorem discharges
   table/oracle events internally. Do not assume phase execution, output or free.
5. Bind the small source expressions to machine operations before arithmetic.
   Derive every range/cast guard from the preceding checked stage. Recombine
   `statement_sequence prefix Sskip` with the actual suffix using the existing
   exact spine lemma, not a differently-associated sequence.

## Next source/value obligations

Authoritative C: non-ASM `C/secp256k1/scalar_4x64_impl.h`, after p4 assignment.
Authoritative AST: original `C.jets_secp.f_secp256k1_scalar_reduce_512`.

- Extract the actual third stage through `_c`, before the final
  `scalar_reduce(r, c + scalar_check_overflow(r))` call. Verify the boundary
  against the actual generated spine rather than assuming `_c` is unique.
- Start with actual typed p0..p3 Vlong and p4 Vint checkpoint values. Reuse
  the same original 15-local environment and owned output/input regions.
- Prove the actual u128 from_u64/accum_mul/to_u64/rshift64/accum_u64/hi_u64
  sequence. The helper execution, unsigned product and shift oracle proofs
  already exist; keep actual stores and current-memory loads connected.
- Reconstruct four output limbs plus c as low256(second)+p4*D. With p4<=2,
  derive c<=1 and pre-final value <2*canonical_order. If c=1, wrapped low256
  is below the order, so its actual overflow flag is zero. Thus c+overflow is
  0 or 1. Reuse accepted overflow and final scalar_reduce bridges.
- Every fold preserves residue because radix=canonical_order+D. The sharp
  constants and first/second bridge bounds are already proved in the frozen
  `scalar-reduce512-bounds` archive.
- Finish actual function entry, return and freeing of the original 15 locals;
  current root assumes their legitimate entry representation and env match.
  A body-prefix exec_stmt result is not an eval_funcall theorem.
- Then compose original scalar product, public readers/callers/writers/free,
  and **literal canonical Simplicity** multiply/square programs. Integer modulo
  identities alone cannot earn a public coverage entry.

## Diagnosed conversion failures

Direct monolithic source comparison expands first-fold expressions inside
the second fold, including in weak-head reduction of p3's actual lookup.
Typed semantic checkpoints avoid that growth without altering C.

For stage entry, the allocator/binder match is not cheaply convertible merely
because the final proof obligation has no visible subgoals. Use the general
`extract_stage_entry` lemma and keep **xalloc, xbind and compact_stmt opaque
while applying the equality**. Without xalloc/xbind opacity, conversion eagerly
replays the closed allocator/binder; even a bounded 60-second Qed experiment
failed. The final source uses the original ten-second limits and compiles.
Restore transparency only for the small checked metadata computation. This
changes reduction strategy, not axioms, code, statements or kernel checking.

The PTree.gsspec comparison is `peq query_id set_id`, not the opposite order.
Preserve `den` around a compound symbolic sum when rewriting its proved
denotation; broad cbn unfolds that sum and destroys the matching subterm.
Keep run/state definitions opaque during execution-theorem applications.

Main coverage remains 351/533. Isolated scalar-add acceptance is 359/533 with
exact main integration/verification pending. Claude owns Elements and shared
memcpy/SHA/constructibility obligations. Do not change their files or registries.
Preserve all unrelated staged/unstaged work. Local signed commits only.
