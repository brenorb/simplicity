(** Three actual original reads into one point, preserving earlier coordinates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_canonical_normalize C.jet_secp_read_fe_rebase.
Require Import C.jet_secp_point_write_run C.jet_secp_point_read_run.
Require Import C.jet_secp_point_read_owned C.jet_secp_point_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Definition point_canonical_limbs (value : Ty.tySem (Word 8)) :=
  map Int64.repr (fe_limbs_of (@toZ (WordToZ 8)
    (@canonical_fe_normalize Alg.CoreFunSem value))).
Lemma point_canonical_limbs_length value : length (point_canonical_limbs value) = 5%nat.
Proof. reflexivity. Qed.

Theorem eval_point_three_readers m0 bd dbase bw outedge cursor N cap bi edge rc
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
  exists mx my mz,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_read_fe)
      [Vptr ba (Ptrofs.repr 40);Vptr bl Ptrofs.zero] E0 my Vundef /\
    Clight2.eval_funcall secp_ge my (Internal f_read_fe)
      [Vptr ba (Ptrofs.repr 80);Vptr bl Ptrofs.zero] E0 mz Vundef /\
    fe_at mz ba 0 (point_canonical_limbs x) /\
    fe_at mz ba 40 (point_canonical_limbs y) /\
    fe_at mz ba 80 (point_canonical_limbs z) /\
    frame_fields_at mz bl 0 bi edge (rc+768) /\
    Mem.range_perm mz ba 0 128 Cur Freeable /\ Mem.range_perm mz bl 0 16 Cur Freeable /\
    invA m0 bd dbase bw outedge cursor N bi (rc+512) false [] cap
      (read_fe_rho (frame_input_word_bits z) (rc+512))
      (read_fe_log bi (Ptrofs.repr edge)) mz /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (point_read_initial_regs PointX bi (Ptrofs.repr edge)) m) m mx /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (point_read_initial_regs PointY bi (Ptrofs.repr edge)) mx) mx my /\
    lframe (frame (extA m0 bd bw bi) [(ba,0);(bl,0)]
      (point_read_initial_regs PointZ bi (Ptrofs.repr edge)) my) my mz.
Proof.
  intros HO HX HY HZ Hrc HM HFA HFL HSource HSep HXS HInv.
  destruct (eval_point_read_fe_canonical PointX m0 bd dbase bw outedge cursor N cap
    bi edge rc x m ba bl HO HX Hrc ltac:(lia) HFA HFL HSource HSep HXS HInv)
    as (mx & HCallX & HFieldX & HSourceX & HFreeAX & HFreeLX & HInvX & HFrameX).
  pose proof (read_fe_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge rc (rc+256) cap x y mx HInvX) as HNextY.
  destruct (eval_point_read_fe_canonical PointY m0 bd dbase bw outedge cursor N cap
    bi edge (rc+256) y mx ba bl HO HY ltac:(lia) ltac:(lia)
    HFreeAX HFreeLX HSourceX HSep HXS HNextY)
    as (my & HCallY & HFieldY & HSourceY & HFreeAY & HFreeLY & HInvY & HFrameY).
  replace (rc+256+256) with (rc+512) in HSourceY by lia.
  assert (HFieldXY : fe_at my ba 0 (point_canonical_limbs x)).
  { eapply (point_read_preserves_field mx my m0 bd bw bi ba bl edge PointY PointX).
    - discriminate.
    - exact HSep.
    - rewrite point_canonical_limbs_length; lia.
    - exact HFieldX.
    - exact HFreeAY.
    - exact HXS.
    - exact HFrameY. }
  pose proof (read_fe_final_inv_to_next_initial m0 bd dbase bw outedge cursor N bi
    edge (rc+256) (rc+512) cap y z my HInvY) as HNextZ.
  destruct (eval_point_read_fe_canonical PointZ m0 bd dbase bw outedge cursor N cap
    bi edge (rc+512) z my ba bl HO HZ ltac:(lia) ltac:(lia)
    HFreeAY HFreeLY HSourceY HSep HXS HNextZ)
    as (mz & HCallZ & HFieldZ & HSourceZ & HFreeAZ & HFreeLZ & HInvZ & HFrameZ).
  replace (rc+512+256) with (rc+768) in HSourceZ by lia.
  assert (HFieldXZ : fe_at mz ba 0 (point_canonical_limbs x)).
  { eapply (point_read_preserves_field my mz m0 bd bw bi ba bl edge PointZ PointX).
    - discriminate.
    - exact HSep.
    - rewrite point_canonical_limbs_length; lia.
    - exact HFieldXY.
    - exact HFreeAZ.
    - exact HXS.
    - exact HFrameZ. }
  assert (HFieldYZ : fe_at mz ba 40 (point_canonical_limbs y)).
  { eapply (point_read_preserves_field my mz m0 bd bw bi ba bl edge PointZ PointY).
    - discriminate.
    - exact HSep.
    - rewrite point_canonical_limbs_length; lia.
    - exact HFieldY.
    - exact HFreeAZ.
    - exact HXS.
    - exact HFrameZ. }
  exists mx, my, mz.
  split; [exact HCallX|]. split; [exact HCallY|]. split; [exact HCallZ|].
  split; [exact HFieldXZ|]. split; [exact HFieldYZ|]. split; [exact HFieldZ|].
  split; [exact HSourceZ|]. split; [exact HFreeAZ|]. split; [exact HFreeLZ|].
  split; [exact HInvZ|]. split; [exact HFrameX|]. split; assumption.
Qed.
Print Assumptions eval_point_three_readers.
