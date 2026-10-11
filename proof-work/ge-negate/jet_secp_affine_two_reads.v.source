(** Two actual field reads into the real affine allocation, preserving X. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_canonical_normalize C.jet_secp_read_fe_rebase.
Require Import C.jet_secp_point_write_run C.jet_secp_point_three_reads.
Require Import C.jet_secp_owned_read_run C.jet_secp_owned_read_canonical C.jet_secp_owned_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Theorem eval_affine_two_readers m0 bd dbase bw outedge cursor N cap bi edge rc
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
  exists mx my,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_read_fe)
      [Vptr ba (Ptrofs.repr 40);Vptr bl Ptrofs.zero] E0 my Vundef /\
    fe_at my ba 0 (point_canonical_limbs x) /\ fe_at my ba 40 (point_canonical_limbs y) /\
    frame_fields_at my bl 0 bi edge (rc+512) /\
    Mem.range_perm my ba 0 88 Cur Freeable /\ Mem.range_perm my bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi (rc+256) false [] cap
      (read_fe_rho (frame_input_word_bits y) (rc+256)) (read_fe_log bi (Ptrofs.repr edge)) my /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (owned_read_initial_regs 88 PointX bi (Ptrofs.repr edge)) m) m mx /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (owned_read_initial_regs 88 PointY bi (Ptrofs.repr edge)) mx) mx my.
Proof.
  intros HO HX HY Hrc HM HFA HFL HSource HSep HXS HInv.
  destruct (eval_owned_read_fe_canonical 88 PointX m0 bd dbase bw outedge cursor N cap
    bi edge rc x m ba bl ltac:(change (0+40 <= 88);lia) HO HX Hrc ltac:(lia)
    HFA HFL HSource HSep HXS HInv)
    as (mx & HCallX & HFieldX & HSourceX & HFreeAX & HFreeLX & HInvX & HFrameX).
  pose proof (read_fe_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge rc (rc+256) cap x y mx HInvX) as HNextY.
  destruct (eval_owned_read_fe_canonical 88 PointY m0 bd dbase bw outedge cursor N cap
    bi edge (rc+256) y mx ba bl ltac:(change (40+40 <= 88);lia) HO HY ltac:(lia) ltac:(lia)
    HFreeAX HFreeLX HSourceX HSep HXS HNextY)
    as (my & HCallY & HFieldY & HSourceY & HFreeAY & HFreeLY & HInvY & HFrameY).
  replace (rc+256+256) with (rc+512) in HSourceY by lia.
  assert (HFieldXY : fe_at my ba 0 (point_canonical_limbs x)).
  { eapply (owned_read_preserves_field 88 mx my m0 bd bw bi ba bl edge PointY PointX).
    - change (0+40 <= 88); lia.
    - discriminate.
    - exact HSep.
    - rewrite point_canonical_limbs_length; lia.
    - exact HFieldX.
    - exact HFreeAY.
    - exact HXS.
    - exact HFrameY. }
  exists mx,my; split; [exact HCallX|]; split; [exact HCallY|].
  split; [exact HFieldXY|]; split; [exact HFieldY|]; split; [exact HSourceY|].
  split; [exact HFreeAY|]; split; [exact HFreeLY|]; split; [exact HInvY|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_affine_two_readers.
