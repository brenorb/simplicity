(** The original affine writer after an arbitrary already-written prefix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_point_write_field C.jet_secp_point_write_run.
Require Import C.jet_secp_owned_write_field C.jet_secp_owned_write_preservation.
Require Import C.jet_secp_write_ge_body.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque Simplicity.Translate.encode.

Theorem eval_affine_two_writes_from_prefix m0 bd base bw edge cursor N bi (rc : Z)
    written0 outs0 m b fx fy :
  write_frame_at m0 bd base bw edge cursor N -> Z.of_nat (length outs0)+512 <= N ->
  finv m0 bd base bw edge cursor N bi m written0 outs0 ->
  point_field_bounds fx -> point_field_bounds fy ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  Mem.range_perm m b 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mx mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr base);Vptr b (Ptrofs.repr 0)] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr base);Vptr b (Ptrofs.repr 40)] E0 mf Vundef /\
    finv m0 bd base bw edge cursor N bi mf true
      (outs0 ++ (Simplicity.Translate.encode (point_field_output fx) ++
                 Simplicity.Translate.encode (point_field_output fy))) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros Output Cap Inv BoundX BoundY FieldX FieldY Free Sep.
  set (outX := outs0 ++ Simplicity.Translate.encode (point_field_output fx)).
  assert (LenX : length outX = (length outs0 + 256)%nat).
  { unfold outX; rewrite app_length, Simplicity.Translate.encode_length; reflexivity. }
  assert (InvX : invA m0 bd base bw edge cursor N bi rc written0 outs0
      256 (point_field_rho fx rc) [] m).
  { unfold invA; rewrite Bool.orb_false_r.
    change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd base bw edge cursor N bi m written0 (outs0++[]) /\
      Z.of_nat (length outs0)+256<=N /\ 0<=256).
    rewrite app_nil_r; split; [reflexivity|]; split; [exact Inv|]; split; lia. }
  destruct (eval_owned_bounded_field_write 88 m0 bd base bw edge cursor N bi rc fx written0 outs0
      PointX m b ltac:(cbn;lia) Output BoundX FieldX Free Sep InvX)
    as (mx & CallX & FinX & FreeX & FrameX).
  change (finv m0 bd base bw edge cursor N bi mx true outX) in FinX.
  assert (FieldYX : fe_at mx b 40 (point_field_limbs fy)).
  { exact (owned_write_preserves_field 88 m mx m0 bd bw bi b PointX PointY (point_field_limbs fy)
      ltac:(discriminate) ltac:(cbn;lia) eq_refl FieldY FreeX Sep FrameX). }
  assert (InvY : invA m0 bd base bw edge cursor N bi rc true outX
      256 (point_field_rho fy rc) [] mx).
  { change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd base bw edge cursor N bi mx true (outX++[]) /\
      Z.of_nat (length outX)+256<=N /\ 0<=256).
    rewrite app_nil_r, LenX, Nat2Z.inj_add;
    split; [reflexivity|]; split; [exact FinX|]; split; lia. }
  destruct (eval_owned_bounded_field_write 88 m0 bd base bw edge cursor N bi rc fy true outX
      PointY mx b ltac:(cbn;lia) Output BoundY FieldYX FreeX Sep InvY)
    as (mf & CallY & FinY & FreeY & FrameY).
  exists mx,mf; split; [exact CallX|]; split; [exact CallY|].
  split.
  - unfold outX in FinY; rewrite <- app_assoc in FinY; exact FinY.
  - split; [exact FreeY|].
    eapply lframe_trans; eapply owned_write_outside_owner; eassumption.
Qed.

Theorem eval_write_ge_from_prefix m0 bd base bw edge cursor N bi (rc : Z)
    written0 outs0 m b fx fy :
  write_frame_at m0 bd base bw edge cursor N -> Z.of_nat (length outs0)+512 <= N ->
  finv m0 bd base bw edge cursor N bi m written0 outs0 ->
  point_field_bounds fx -> point_field_bounds fy ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  Mem.range_perm m b 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_ge)
      [Vptr bd (Ptrofs.repr base);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd base bw edge cursor N bi mf true
      (outs0 ++ (Simplicity.Translate.encode (point_field_output fx) ++
                 Simplicity.Translate.encode (point_field_output fy))) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros Output Cap Inv BoundX BoundY FieldX FieldY Free Sep.
  destruct (eval_affine_two_writes_from_prefix m0 bd base bw edge cursor N bi rc
      written0 outs0 m b fx fy Output Cap Inv BoundX BoundY FieldX FieldY Free Sep)
    as (mx & mf & CallX & CallY & Final & FreeF & Frame).
  exists mf; split; [eapply eval_write_ge_from_calls; eassumption|].
  split; [exact Final|]; split; assumption.
Qed.
