(** Original read_gej execution from initial storage/input, not assumed calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import Simplicity.Word.
Require Simplicity.Bit Simplicity.Alg.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_input_layout.
Require Import C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_canonical_zero.
Require Import C.jet_secp_point_write_run C.jet_secp_point_read_run C.jet_secp_point_three_reads.
Require Import C.jet_secp_point_zero_owned C.jet_secp_gej_read_flag_store.
Require Import C.jet_secp_point_source_preservation C.jet_secp_read_gej_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_is_zero secp_ge.

Theorem eval_read_gej_canonical_owned m0 bd dbase bw outedge cursor N cap bi edge rc
    (x y z : Ty.tySem (Word 8)) m ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0 <= rc -> rc+768 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] cap
    (read_fe_rho (frame_input_word_bits x) rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_gej)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
    Mem.load Mint32 mf ba 120 =
      Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) /\
    frame_fields_at mf bl 0 bi edge (rc+768) /\
    Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi (rc+512) false [] cap
      (read_fe_rho (frame_input_word_bits z) (rc+512)) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HInv.
  destruct (eval_point_three_readers m0 bd dbase bw outedge cursor N cap bi edge rc
    x y z m ba bl HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HInv)
    as (mx & my & mz & HCallX & HCallY & HCallZ & HFieldX & HFieldY & HFieldZ &
        HSourceZ & HFreeAZ & HFreeLZ & HInvZ & HFrameX & HFrameY & HFrameZ).
  destruct (eval_point_zero_canonical PointZ mz ba z HFieldZ HFreeAZ)
    as (mt & HZero & HFreeAT & HZeroFrame).
  destruct (point_lframe_preserves_source mz mt ba bl bi edge (rc+768)
    HSep HSourceZ HFreeLZ HZeroFrame) as [HSourceT HFreeLT].
  pose proof (point_lframe_preserves_inv m0 bd dbase bw outedge cursor N cap bi
    (rc+512) false [] (read_fe_rho (frame_input_word_bits z) (rc+512))
    (read_fe_log bi (Ptrofs.repr edge)) mz mt ba bl HO HXS HInvZ HZeroFrame) as HInvT.
  set (flag := bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z))).
  set (le := PTree.set _t'1 (Vint flag) (read_gej_env ba bl)).
  assert (HR : le!_r = Some (Vptr ba (Ptrofs.repr 0))).
  { unfold le, read_gej_env. rewrite !PTree.gso by discriminate; apply PTree.gss. }
  assert (HT : le!_t'1 = Some (Vint flag)).
  { unfold le; apply PTree.gss. }
  destruct (exec_gej_read_flag_owned le mt ba 0 flag ltac:(lia) ltac:(exists 0;lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HR HT HFreeAT)
    as (mf & HFlagStmt & HFlagLoad & HFreeAF & HFlagLoads & HFlagPerms & HFlagValid).
  assert (HFlagFrame : lframe (fun b _ => b <> ba) mt mf).
  { split.
    - intros chunk b ofs HV HP. apply HFlagLoads. left.
      apply (HP ofs); pose proof (size_chunk_pos chunk); lia.
    - split.
      + intros b ofs k p HV HP HPerm. apply (proj2 (HFlagPerms b ofs k p)); exact HPerm.
      + exact HFlagValid. }
  destruct (point_lframe_preserves_source mt mf ba bl bi edge (rc+768)
    HSep HSourceT HFreeLT HFlagFrame) as [HSourceF HFreeLF].
  pose proof (point_lframe_preserves_inv m0 bd dbase bw outedge cursor N cap bi
    (rc+512) false [] (read_fe_rho (frame_input_word_bits z) (rc+512))
    (read_fe_log bi (Ptrofs.repr edge)) mt mf ba bl HO HXS HInvT HFlagFrame) as HInvF.
  exists mf; split.
  - eapply eval_read_gej_from_calls; [exact HCallX|exact HCallY|exact HCallZ|exact HZero|exact HFlagStmt].
  - split; [exact HFlagLoad|]. split; [exact HSourceF|].
    split; [exact HFreeAF|]. split; [exact HFreeLF|]. split; [exact HInvF|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HFrameX|].
      intros b pos [HA [HL HE]] HV; split; [exact HV|]; split; [|exact HE].
      apply point_read_outside_foot; assumption.
    + eapply lframe_trans.
      * eapply lframe_implies; [exact HFrameY|].
        intros b pos [HA [HL HE]] HV; split; [exact HV|]; split; [|exact HE].
        apply point_read_outside_foot; assumption.
      * eapply lframe_trans.
        -- eapply lframe_implies; [exact HFrameZ|].
           intros b pos [HA [HL HE]] HV; split; [exact HV|]; split; [|exact HE].
           apply point_read_outside_foot; assumption.
        -- eapply lframe_trans.
           ++ eapply lframe_implies; [exact HZeroFrame|].
              intros b pos [HA [HL HE]] HV; exact HA.
           ++ eapply lframe_implies; [exact HFlagFrame|].
              intros b pos [HA [HL HE]] HV; exact HA.
Qed.
Timeout 60 Print Assumptions eval_read_gej_canonical_owned.
