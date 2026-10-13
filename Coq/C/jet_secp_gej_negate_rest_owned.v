(** Original public remainder: all read/helper/write calls are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_toZ C.jet_word_repr C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout C.jet_output_layout.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_gej_public_entry C.jet_secp_public_body C.jet_secp_point_three_reads.
Require Import C.jet_secp_point_source_preservation C.jet_secp_read_gej_fields.
Require Import C.jet_secp_gej_negate_point_output C.jet_secp_write_gej_negated_literal.
Require Import C.jet_secp_gej_negate_literal C.jet_secp_gej_negate_boundary.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_normalize canonical_fe_is_zero Simplicity.Translate.encode.

Theorem exec_gej_negate_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    (x y z : Ty.tySem (Word 8)) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0 <= rc -> rc+768 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 768
    (read_fe_rho (frame_input_word_bits x) rc) [] m ->
  exists mf,
    Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m gej_negate_public_rest E0
      le mf (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_negate Alg.CoreFunSem ((x,y),z))) /\
    Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HD HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HI.
  destruct (eval_read_gej_canonical_fields m0 bd dbase bw outedge cursor N 768 bi edge rc
    x y z m ba bl HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HI)
    as (mr & HRead & HFieldX & HFieldY & HFieldZ & HFlag & HSourceR &
      HFreeAR & HFreeLR & HInvR & HReadFrame).
  destruct (eval_gej_negate_point_output mr ba
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y))
    (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))
    (point_canonical_limbs x) (point_canonical_limbs z)
    (word_toZ_range 8 _) (point_canonical_limbs_length x) (point_canonical_limbs_length z)
    HFieldX HFieldY HFieldZ HFreeAR HFlag)
    as (mn & HNeg & HFieldXN & HFieldYN & HFieldZN & HFreeAN & HFlagN & HNegFrame).
  destruct (point_lframe_preserves_source mr mn ba bl bi edge (rc+768)
    HSep HSourceR HFreeLR HNegFrame) as [HSourceN HFreeLN].
  pose proof (point_lframe_preserves_inv m0 bd dbase bw outedge cursor N 768 bi
    (rc+512) false [] (read_fe_rho (frame_input_word_bits z) (rc+512))
    (read_fe_log bi (Ptrofs.repr edge)) mr mn ba bl HO HXS HInvR HNegFrame) as HInvN.
  destruct HInvN as [_ [HCurrent [HCapacity _]]].
  change (finv m0 bd dbase bw outedge cursor N bi mn false []) in HCurrent.
  change (768 <= N) in HCapacity.
  assert (HS : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r HR. destruct r; [exact (HXS 0%nat ltac:(cbn;lia))|cbn in HR;lia]. }
  destruct (eval_write_gej_negated_literal m0 bd dbase bw outedge cursor N bi rc mn ba
    x y z HO HCapacity HCurrent HFieldXN HFieldYN HFieldZN HFreeAN HS)
    as (mf & HWrite & HFinal & HFreeAF & HWriteFrame).
  assert (HFreeLF : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HPos. apply (proj1 (proj2 HWriteFrame)).
    - eapply Mem.perm_valid_block; apply (HFreeLN 0);lia.
    - split; [congruence|exact (HXS 1%nat ltac:(cbn;lia))].
    - apply HFreeLN;exact HPos. }
  exists mf; split.
  - exact (exec_gej_negate_rest_from_calls le m mr mn mf bl ba bd dbase HD HRead HNeg HWrite).
  - split; [exact HFinal|]. split; [exact HFreeAF|]. split; [exact HFreeLF|].
    eapply lframe_trans; [exact HReadFrame|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HNegFrame|].
      intros b pos [HA [HL HE]] HV;exact HA.
    + eapply lframe_implies; [exact HWriteFrame|].
      intros b pos [HA [HL HE]] HV;split;assumption.
Qed.
Timeout 60 Print Assumptions exec_gej_negate_rest_owned.
