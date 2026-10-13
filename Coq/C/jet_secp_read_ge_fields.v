(** Entire original affine reader derived from input/storage, including zero flag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Word.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout.
Require Import C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_body C.jet_secp_wrapper_run.
Require Import C.jet_secp_point_write_run C.jet_secp_point_three_reads C.jet_secp_point_source_preservation.
Require Import C.jet_secp_owned_read_run C.jet_secp_owned_read_preservation C.jet_secp_owned_field_transport.
Require Import C.jet_secp_affine_two_reads C.jet_secp_affine_read_flag C.jet_secp_read_ge_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_read_ge_canonical_fields m0 bd dbase bw outedge cursor N cap bi edge rc
    (x y : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits x) rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_ge)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
    fe_at mf ba 0 (point_canonical_limbs x) /\ fe_at mf ba 40 (point_canonical_limbs y) /\
    Mem.load Mint32 mf ba 80 = Some (Vint Int.zero) /\
    frame_fields_at mf bl 0 bi edge (rc+512) /\
    Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi (rc+256) false [] cap
      (read_fe_rho (frame_input_word_bits y) (rc+256)) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HO HX HY Hrc HM HFA HFL HSource HSep HXS HInv.
  destruct (eval_affine_two_readers m0 bd dbase bw outedge cursor N cap bi edge rc
    x y m ba bl HO HX HY Hrc HM HFA HFL HSource HSep HXS HInv)
    as (mx & my & HCallX & HCallY & HFieldX & HFieldY & HSourceY & HFreeAY & HFreeLY &
      HInvY & HFrameX & HFrameY).
  assert (HR : (read_ge_env ba bl)!_r = Some (Vptr ba Ptrofs.zero)).
  { unfold read_ge_env; rewrite PTree.gso by discriminate; apply PTree.gss. }
  destruct (exec_affine_read_flag_owned (read_ge_env ba bl) my ba HR HFreeAY)
    as (mf & HFlagStmt & HFlagLoad & HFreeAF & HFlagLoads & HFlagFrame).
  destruct (point_lframe_preserves_source my mf ba bl bi edge (rc+512)
    HSep HSourceY HFreeLY HFlagFrame) as (HSourceF & HFreeLF).
  pose proof (point_lframe_preserves_inv m0 bd dbase bw outedge cursor N cap bi
    (rc+256) false [] (read_fe_rho (frame_input_word_bits y) (rc+256))
    (read_fe_log bi (Ptrofs.repr edge)) my mf ba bl HO HXS HInvY HFlagFrame) as HInvF.
  assert (HFieldFlag : forall offset xs,
    offset+40 <= 80 -> (length xs <= 5)%nat -> fe_at my ba offset xs -> fe_at mf ba offset xs).
  { intros offset xs HFit HLen HField.
    eapply (owned_field_load_transport offset 88 my mf ba xs);
      [lia|exact HLen|exact HField|exact HFreeAF|].
    intros i Hi; apply HFlagLoads; right;left; change (size_chunk Mint64) with 8; lia. }
  exists mf; split.
  - eapply eval_read_ge_from_calls; eassumption.
  - split; [exact (HFieldFlag 0 _ ltac:(lia) ltac:(rewrite point_canonical_limbs_length;lia) HFieldX)|].
    split; [exact (HFieldFlag 40 _ ltac:(lia) ltac:(rewrite point_canonical_limbs_length;lia) HFieldY)|].
    split; [exact HFlagLoad|]; split; [exact HSourceF|]; split; [exact HFreeAF|].
    split; [exact HFreeLF|]; split; [exact HInvF|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HFrameX|].
      intros b pos [HA [HL HE]] HV; split; [exact HV|]; split; [|exact HE].
      intro HFoot; destruct (owned_read_foot_bounds 88 PointX ba bl bi (Ptrofs.repr edge) b pos HFoot)
        as [HB|[HB _]]; congruence.
    + eapply lframe_trans.
      * eapply lframe_implies; [exact HFrameY|].
        intros b pos [HA [HL HE]] HV; split; [exact HV|]; split; [|exact HE].
        intro HFoot; destruct (owned_read_foot_bounds 88 PointY ba bl bi (Ptrofs.repr edge) b pos HFoot)
          as [HB|[HB _]]; congruence.
      * eapply lframe_implies; [exact HFlagFrame|].
        intros b pos [HA [HL HE]] HV; exact HA.
Qed.
Timeout 60 Print Assumptions eval_read_ge_canonical_fields.
