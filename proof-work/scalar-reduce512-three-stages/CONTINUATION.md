# Continue with the final reduction and complete function boundary

Update: the final reduction and complete original function entry/allocation/
return/free/current-memory numeric boundary are now checked in
`../scalar-reduce512-final/CONTINUATION.md`. Its fresh build, contract/assumption
drivers and independent kernel check passed. The historical final-reduction
and function-boundary TODOs below are superseded; public multiply/square and
literal Simplicity/evaluator-frame composition remain open.

Last verified declaration:
`exec_reduce512_first_three_stages`. The six archived modules compile fully.
Their receipt/reviewer record the fresh build, contracts, assumptions and
independent kernel check. No failing goal remains in these archived files.

Do not restart the monolithic p3 experiment described by the older bounds
handoff: both second and third source/value/execution bridges now compile.
Use typed machine checkpoints, retaining original rho and concrete memory.

## Final actual source slice

Authoritative C: the final call in `C/secp256k1/scalar_4x64_impl.h`.
Authoritative AST: `C.jets_secp.f_secp256k1_scalar_reduce_512`.

1. Define/check the suffix after the actual third-stage `_c` boundary.
   Reconstruct the unchanged body with `statement_sequence` and the existing
   exact-spine execution lemma. Check the final statement/return structure.
2. Start from the third postcondition: four real current-memory output loads,
   actual Vlong c, its [0,1] range and the exact untruncated folded value <2N.
   The input region and 15 original locals remain owned. Preserve r/l pointers.
3. Keep initialized output values. The new suffix reads these cells before
   writing them, so **do not forget output initialization**. If checkpointing
   cells to typed XL leaves, prove denotation-preserving replacement and shape/
   permissions/ownership preservation. `rep_forget_after 2` is appropriate
   only for scratch locals; it retains the first two regions.
4. Execute actual scalar_check_overflow and scalar_reduce, not assumed calls.
   Reuse existing linkage/execution/value lemmas or the proved compact executor.
   The full original reduce512 run has six shift events; this third slice
   accounts for three. Do not silently replace the remaining event log by [].

## Numeric guard and last-call identity

Let R=2^256, N=canonical_group_order, D=R-N, x=stored four-limb value,
c=actual unsigned carry. The checked result gives x+R*c=v, 0<=c<=1, v<2N.

- If c=1 then x<N (since R>N), so actual overflow flag is zero.
- If c=0 then the actual overflow flag is the comparison N<=x.
- Therefore c+overflow is 0 or 1. Establish the **actual narrowing/promotion
  into scalar_reduce's overflow argument**, not merely a decoded bit.
- Reuse `C.jet_secp_scalar_overflow_numeric.scalar_overflow_matches_bound`
  and the exact carrier/output facts. The scalar_reduce canonical-value theorem
  assumes its flag equals the overflow comparison and cannot directly cover
  c=1, where the correct flag is 1 although x<N. Use the more general proved
  `scalar_reduce_weighted_value` with a proved Boolean flag adapter.
- Its machine value is (x+flag*D) mod R. Prove this equals v mod N by the two
  carry cases and actual comparison. This internal integer bridge does not
  replace the public literal specification.
- Chain `second_checkpoint_third_modulo`, `second_fold_bridge_modulo_order`
  and `first_fold_modulo_order` to the original eight-limb input.

## Function and public boundaries still needed

Current root is exec_stmt on already allocated original locals, not
eval_funcall. Establish function entry/argument binding and actual allocation
(`xalloc_sound`), compose the proved whole body, then prove return conversion
and actual freeing of all 15 original locals. Use owned-region free facts;
do not add required execution/free/post-memory assumptions to the public root.
The older full owned exec theorem has no numeric output bridge yet and is not
alone a substitute for the checkpoint-based complete numeric proof.

Then compose the checked original scalar_mul_512 product, reduction, public
readers/callers/writers/free and **literal canonical Simplicity** multiplication/
square roots. Broader evaluator-frame contracts and other jets remain in scope.

## Development details from this milestone

- Include the defining module `C.jet_secp_frame` for `cell_sx`; Require Import
  of a consumer does not transitively re-export that name.
- The short typed third slice's whole source equality closes by bounded
  reflexivity. Trying `f_equal2` on a still-folded map-based output list failed
  at its list head; unlike the old huge second expression, this source is small.
- Preserve the raw unsigned p4 cast and the multiplication's actual operand
  order. Third shift syntax includes XLc zero, not the macro's XI2L zero.
- Normalize only the outer nth_error after lifting map equality; an explicit
  `change` exposes it without unfolding the machine expressions.
- Name unsigned range hypotheses. Anonymous pose proof names H0/H1 can collide
  with column-value assertions. Rewrite each C0/C1 constant only in hypotheses
  containing it; a combined rewrite in both fails on the missing subterm.
- All tactics remain bounded at ten seconds. No admissions or unchecked proof
  escapes, source changes, registry edits or public coverage claims were used.

Main coverage is 351/533, not the isolated scalar-add 359/533 acceptance.
Preserve its pending exact main integration and all unrelated staged/unstaged
SHA/range/field-negate work. Claude owns Elements foundation/getters and shared
memcpy/SHA/constructibility; this scalar work does not overlap. Local signed
atomic commits only, no remote pushes.
