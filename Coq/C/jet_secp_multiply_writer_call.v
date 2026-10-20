(** Original in-place multiplication and actual normalization/serialization writer.
    Reader and literal Simplicity-program composition are separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_local_regions C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_fe_nv C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_first_arithmetic C.jet_secp_multiply_finish_execute C.jet_secp_multiply_finish_product C.jet_secp_multiply_call_call C.jet_secp_multiply_wrapper_call.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_writer_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge original_finish_words.

Theorem eval_original_field_mul_then_write m0 bd dbase bw edge cursor N bi rc w0 outs0
    rho beta m :
  write_frame_at m0 bd dbase bw edge cursor N ->
  field_input_bounds rho -> rep rho beta field_mul_regs m ->
  xsep (extA m0 bd bw bi) beta ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 (cursor_rho rc) [] m ->
  exists mm mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mm Vundef /\
    Clight2.eval_funcall secp_ge mm (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr (blk beta 0) Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (product_word rho)) /\
    fe_at mf (blk beta 1) (bas beta 1) (words5 (second_input rho)) /\
    Mem.range_perm mf (blk beta 0) 0 40 Cur Freeable /\
    Mem.range_perm mf (blk beta 1) 0 40 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) beta field_mul_regs m) m mf.
Proof.
  intros HO HB HR HS HI.
  pose proof (proj1 HR) as HLen; change (length beta = 2%nat) in HLen.
  destruct (eval_original_field_mul_wrapper rho beta m HR) as (mm & HM & HRep & HLoads & HF).
  destruct (multiplier_output_storage rho beta mm HRep) as [HBase HFree].
  destruct (multiplier_second_storage rho beta mm HRep) as [HBaseSecond HFreeSecond].
  pose proof (multiplier_output_blocks_distinct rho beta mm HRep) as HDistinct.
  pose proof (multiplier_second_fe_at rho beta mm HRep) as HSecond.
  assert (HExt : lframe (fun b' _ => extA m0 bd bw bi b') m mm).
  { eapply lframe_implies; [exact HF|].
    intros b' pos HE HValid.
    exact (foot_disjoint_external (extA m0 bd bw bi) beta field_mul_regs
      (proj1 HR) HS b' pos HE). }
  pose proof (invA_stable m0 bd dbase bw edge cursor N bi rc w0 outs0 256 HO
    (cursor_rho rc) [] m mm HI HExt) as HIM.
  set (wrho := product_writer_rho rho rc).
  assert (HWI : invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 wrho [] mm).
  { unfold invA in *; destruct HIM as [_ HRest]; split; [reflexivity|exact HRest]. }
  assert (HSW : xsep (extA m0 bd bw bi) [(blk beta 0, 0)]).
  { intros r Hr; destruct r as [|r].
    - apply (HS 0%nat); rewrite HLen; lia.
    - cbn in Hr; lia. }
  pose proof (multiplier_writer_rep rho beta mm rc HRep) as HWR.
  pose proof (multiplier_normalizer_bounds rho HB) as HBounds.
  destruct (eval_local_wide_write_fe m0 bd dbase bw edge cursor N bi rc
    (original_finish_words rho 0%nat) (original_finish_words rho 1%nat)
    (original_finish_words rho 2%nat) (original_finish_words rho 3%nat)
    (original_finish_words rho 4%nat) w0 outs0 mm [(blk beta 0, 0)] HO
    (HBounds 0%nat ltac:(lia)) (HBounds 1%nat ltac:(lia))
    (HBounds 2%nat ltac:(lia)) (HBounds 3%nat ltac:(lia))
    (HBounds 4%nat ltac:(lia)) HWR HSW HWI)
    as (mf & HW & HFinal & HRepFinal & HWriteFrame).
  rewrite product_writer_output in HFinal by exact HB.
  assert (HVSecond : Mem.valid_block mm (blk beta 1)).
  { eapply Mem.perm_valid_block; apply (HFreeSecond 0); lia. }
  assert (HOther : lframe (fun b' _ => b' = blk beta 1) mm mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros b' pos -> HValid; split; [exact HVSecond|]; split.
    - intro HFoot; apply local_writer_foot_owner in HFoot; congruence.
    - apply (HS 1%nat); rewrite HLen; lia. }
  pose proof (fe_at_on_unchanged_block mm mf _ _ _ HSecond HOther) as HSecondFinal.
  assert (HFreeSecondFinal : Mem.range_perm mf (blk beta 1) 0 40 Cur Freeable).
  { intros pos HP; eapply (proj1 (proj2 HOther));
      [exact HVSecond|reflexivity|apply HFreeSecond; exact HP]. }
  change (rep wrho [(blk beta 0, 0)]
    (sregs (fst (rsel wrho (lay [(blk beta 0, 0)])
      (local_write_result bd (Ptrofs.repr dbase))))) mf) in HRepFinal.
  destruct (local_write_selected_storage wrho (lay [(blk beta 0, 0)]) bd (Ptrofs.repr dbase))
    as [HCount HStorage].
  destruct (rep_free_region wrho [(blk beta 0, 0)] _ mf 0 40 HRepFinal
    ltac:(rewrite HCount; lia) HStorage) as [_ HFreeFinal].
  assert (HMOutside : lframe (frame (extA m0 bd bw bi) beta field_mul_regs m) m mm).
  { eapply lframe_implies; [exact HF|]. intros b' pos [_ [HOutside _]] HValid; exact HOutside. }
  assert (HWOutside : lframe (frame (extA m0 bd bw bi) beta field_mul_regs m) mm mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros b' pos [HValid [HOutside HNotExt]] HV.
    split; [exact (proj2 (proj2 HF) b' HValid)|]; split; [|exact HNotExt].
    intro HFoot; apply HOutside; apply local_writer_foot_in_multiplier; assumption. }
  exists mm, mf; split; [exact HM|]; split; [exact HW|]; split; [exact HFinal|];
    split; [exact HSecondFinal|]; split; [exact HFreeFinal|]; split; [exact HFreeSecondFinal|].
  eapply lframe_trans; eassumption.
Qed.
