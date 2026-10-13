(** Original affine public remainder: all read/negate/write calls are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_toZ C.jet_word_repr C.jet_exec C.jet_encoding C.jet_input_layout C.jet_output_layout.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_secp_canonical_normalize C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_public_body C.jet_secp_point_three_reads C.jet_secp_point_source_preservation.
Require Import C.jet_secp_read_ge_fields C.jet_secp_affine_negate_call C.jet_secp_write_ge_negated_literal.
Require Import C.jet_secp_gej_negate_literal C.jet_secp_ge_negate_boundary.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_normalize Simplicity.Translate.encode.

Theorem exec_ge_negate_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (x y : Ty.tySem (Word 8)) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 512
    (read_fe_rho (frame_input_word_bits x) rc) [] m ->
  exists mf,
    Clight2.exec_stmt secp_ge (ge_public_env bl ba) le m ge_negate_public_rest E0
      le mf (Out_return (Some (Vint Int.one,tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_ge_negate Alg.CoreFunSem (x,y))) /\
    Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HD HO HX HY Hrc HM HFA HFL HSource HSep HXS HI.
  destruct (eval_read_ge_canonical_fields m0 bd dbase bw outedge cursor N 512 bi edge rc
    x y m ba bl HO HX HY Hrc HM HFA HFL HSource HSep HXS HI)
    as (mr & HRead & HFieldX & HFieldY & HFlag & HSourceR &
      HFreeAR & HFreeLR & HInvR & HReadFrame).
  destruct (eval_affine_negate_point_output mr ba
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y))
    (point_canonical_limbs x) Int.zero (word_toZ_range 8 _)
    ltac:(rewrite point_canonical_limbs_length;lia)
    HFieldX HFieldY HFreeAR HFlag)
    as (mn & HNeg & HFieldXN & HFieldYN & HFreeAN & HFlagN & HNegFrame).
  destruct (point_lframe_preserves_source mr mn ba bl bi edge (rc+512)
    HSep HSourceR HFreeLR HNegFrame) as [HSourceN HFreeLN].
  pose proof (point_lframe_preserves_inv m0 bd dbase bw outedge cursor N 512 bi
    (rc+256) false [] (read_fe_rho (frame_input_word_bits y) (rc+256))
    (read_fe_log bi (Ptrofs.repr edge)) mr mn ba bl HO HXS HInvR HNegFrame) as HInvN.
  destruct HInvN as [_ [HCurrent [HCapacity _]]].
  change (finv m0 bd dbase bw outedge cursor N bi mn false []) in HCurrent.
  change (512 <= N) in HCapacity.
  assert (HS : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r HR;destruct r;[exact (HXS 0%nat ltac:(cbn;lia))|cbn in HR;lia]. }
  destruct (eval_write_ge_negated_literal m0 bd dbase bw outedge cursor N bi rc mn ba
    x y HO HCapacity HCurrent HFieldXN HFieldYN HFreeAN HS)
    as (mf & HWrite & HFinal & HFreeAF & HWriteFrame).
  assert (HFreeLF : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HPos;apply (proj1 (proj2 HWriteFrame)).
    - eapply Mem.perm_valid_block;apply (HFreeLN 0);lia.
    - split;[congruence|exact (HXS 1%nat ltac:(cbn;lia))].
    - apply HFreeLN;exact HPos. }
  exists mf;split.
  - exact (exec_ge_negate_rest_from_calls le m mr mn mf bl ba bd dbase HD HRead HNeg HWrite).
  - split;[exact HFinal|];split;[exact HFreeAF|];split;[exact HFreeLF|].
    eapply lframe_trans;[exact HReadFrame|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact HNegFrame|].
      intros b pos [HA [HL HE]] HV;exact HA.
    + eapply lframe_implies;[exact HWriteFrame|].
      intros b pos [HA [HL HE]] HV;split;assumption.
Qed.
Timeout 60 Print Assumptions exec_ge_negate_rest_owned.
