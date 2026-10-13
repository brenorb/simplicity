(** Transport source-frame storage across helpers confined to the point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec C.jet_frame_layout C.jet_output_layout.
Require Import C.jet_secp_frame C.jet_secp_point_read_preservation.
Require Import C.jet_secp_point_read_run C.jet_secp_point_write_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma point_lframe_preserves_source m mf ba bl bi edge rc :
  ba <> bl -> frame_fields_at m bl 0 bi edge rc ->
  Mem.range_perm m bl 0 16 Cur Freeable ->
  lframe (fun b _ => b <> ba) m mf ->
  frame_fields_at mf bl 0 bi edge rc /\
  Mem.range_perm mf bl 0 16 Cur Freeable.
Proof.
  intros HSeparate [HE HC] HP HF.
  assert (HV : Mem.valid_block m bl).
  { eapply Mem.perm_valid_block; apply (HP 0); lia. }
  split.
  - split.
    + rewrite (proj1 HF Mptr bl 0 HV); [exact HE|].
      intros; congruence.
    + rewrite (proj1 HF Mint64 bl (0+8) HV); [exact HC|].
      intros; congruence.
  - intros pos HPos. apply (proj1 (proj2 HF)); [exact HV|congruence|apply HP;exact HPos].
Qed.

Lemma point_read_outside_foot ba bl k bi edge b pos :
  b <> ba -> b <> bl ->
  ~ foot [(ba,0);(bl,0)] (map rshape (point_read_initial_regs k bi edge)) b pos.
Proof.
  intros HA HL HFoot.
  destruct (point_read_foot_bounds k ba bl bi edge b pos HFoot) as [HB|[HB _]];
    congruence.
Qed.

Lemma point_lframe_preserves_inv m0 bd dbase bw outedge cursor N cap bi rc w0 outs rho log m mf ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc w0 outs cap rho log m ->
  lframe (fun b _ => b <> ba) m mf ->
  invA m0 bd dbase bw outedge cursor N bi rc w0 outs cap rho log mf.
Proof.
  intros HO HS HI HF. eapply invA_stable; [exact HO|exact HI|].
  eapply lframe_implies; [exact HF|]. intros b pos HE HV HB; subst b.
  exact (HS 0%nat ltac:(cbn;lia) HE).
Qed.
Print Assumptions point_lframe_preserves_source.
Print Assumptions point_lframe_preserves_inv.
