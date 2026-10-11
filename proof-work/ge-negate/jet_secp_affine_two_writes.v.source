(** Both original field writes over the actual 88-byte affine owner. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_point_write_run C.jet_secp_point_write_field.
Require Import C.jet_secp_owned_write_run C.jet_secp_owned_write_field C.jet_secp_owned_write_preservation.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque Simplicity.Translate.encode.

Theorem eval_affine_two_general_writes m0 bd dbase bw edge cursor N bi (rc : Z) m b fx fy :
  write_frame_at m0 bd dbase bw edge cursor N -> 512 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  point_field_bounds fx -> point_field_bounds fy ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  Mem.range_perm m b 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mx mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 40)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (point_field_output fx) ++
       Simplicity.Translate.encode (point_field_output fy)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HBX HBY HX HY HFree HS.
  set (outX := Simplicity.Translate.encode (point_field_output fx)).
  set (outY := Simplicity.Translate.encode (point_field_output fy)).
  assert (HLX : length outX = 256%nat).
  { unfold outX; rewrite Simplicity.Translate.encode_length; reflexivity. }
  assert (HIX : invA m0 bd dbase bw edge cursor N bi rc false [] 256 (point_field_rho fx rc) [] m).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi m false [] /\
      0+256 <= N /\ 0<=256).
    split; [reflexivity|]; split; [exact HI|]; split; lia. }
  destruct (eval_owned_bounded_field_write 88 m0 bd dbase bw edge cursor N bi rc fx false []
    PointX m b ltac:(cbn;lia) HO HBX HX HFree HS HIX)
    as (mx & HCX & HFinX & HFreeX & HFrameX).
  change (finv m0 bd dbase bw edge cursor N bi mx true outX) in HFinX.
  assert (HYX : fe_at mx b 40 (point_field_limbs fy)).
  { exact (owned_write_preserves_field 88 m mx m0 bd bw bi b PointX PointY (point_field_limbs fy)
      ltac:(discriminate) ltac:(cbn;lia) eq_refl HY HFreeX HS HFrameX). }
  assert (HIY : invA m0 bd dbase bw edge cursor N bi rc true outX 256 (point_field_rho fy rc) [] mx).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi mx true (outX++[]) /\
      Z.of_nat (length outX)+256 <= N /\ 0<=256).
    rewrite app_nil_r, HLX; split; [reflexivity|]; split; [exact HFinX|]; split; lia. }
  destruct (eval_owned_bounded_field_write 88 m0 bd dbase bw edge cursor N bi rc fy true outX
    PointY mx b ltac:(cbn;lia) HO HBY HYX HFreeX HS HIY)
    as (mf & HCY & HFinY & HFreeY & HFrameY).
  exists mx,mf; split; [exact HCX|]; split; [exact HCY|].
  split; [exact HFinY|]; split; [exact HFreeY|].
  eapply lframe_trans; eapply owned_write_outside_owner; eassumption.
Qed.
Print Assumptions eval_affine_two_general_writes.
