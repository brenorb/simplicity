(** Three original writes for arbitrary bounded fields, including negative Y.
    Output is the actual field-writer result; canonical jet bridge is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout.
Require Import C.jet_secp_point_write_run C.jet_secp_point_three_writes C.jet_secp_write_gej_infinity.
Require Import C.jet_secp_point_write_field C.jet_secp_point_write_general_preservation.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque Simplicity.Translate.encode.

Theorem eval_point_three_general_writes m0 bd dbase bw edge cursor N bi (rc : Z) m b fx fy fz :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  point_field_bounds fx -> point_field_bounds fy -> point_field_bounds fz ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  fe_at m b 80 (point_field_limbs fz) ->
  Mem.range_perm m b 0 128 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mx my mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 40)] E0 my Vundef /\
    Clight2.eval_funcall secp_ge my (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 80)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      ((Simplicity.Translate.encode (point_field_output fx) ++
        Simplicity.Translate.encode (point_field_output fy)) ++
        Simplicity.Translate.encode (point_field_output fz)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HBX HBY HBZ HX HY HZ HFree HS.
  set (outX := Simplicity.Translate.encode (point_field_output fx)).
  set (outY := Simplicity.Translate.encode (point_field_output fy)).
  set (outZ := Simplicity.Translate.encode (point_field_output fz)).
  assert (HLX : length outX = 256%nat).
  { unfold outX; rewrite Simplicity.Translate.encode_length; reflexivity. }
  assert (HLY : length outY = 256%nat).
  { unfold outY; rewrite Simplicity.Translate.encode_length; reflexivity. }
  assert (HIX : invA m0 bd dbase bw edge cursor N bi rc false [] 256 (point_field_rho fx rc) [] m).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi m false [] /\
      0+256 <= N /\ 0<=256).
    split; [reflexivity|]; split; [exact HI|]; split; lia. }
  destruct (eval_point_bounded_field_write m0 bd dbase bw edge cursor N bi rc fx false []
    PointX m b HO HBX HX HFree HS HIX) as (mx & HCX & HFinX & HFreeX & HFrameX).
  change (finv m0 bd dbase bw edge cursor N bi mx true outX) in HFinX.
  assert (HYX : fe_at mx b 40 (point_field_limbs fy)).
  { exact (point_write_preserves_field m mx m0 bd bw bi b PointX PointY (point_field_limbs fy)
      ltac:(discriminate) eq_refl HY HFreeX HS HFrameX). }
  assert (HZX : fe_at mx b 80 (point_field_limbs fz)).
  { exact (point_write_preserves_field m mx m0 bd bw bi b PointX PointZ (point_field_limbs fz)
      ltac:(discriminate) eq_refl HZ HFreeX HS HFrameX). }
  assert (HIY : invA m0 bd dbase bw edge cursor N bi rc true outX 256 (point_field_rho fy rc) [] mx).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi mx true (outX++[]) /\
      Z.of_nat (length outX)+256 <= N /\ 0<=256).
    rewrite app_nil_r, HLX; split; [reflexivity|]; split; [exact HFinX|]; split; lia. }
  destruct (eval_point_bounded_field_write m0 bd dbase bw edge cursor N bi rc fy true outX
    PointY mx b HO HBY HYX HFreeX HS HIY) as (my & HCY & HFinY & HFreeY & HFrameY).
  change (finv m0 bd dbase bw edge cursor N bi my true (outX++outY)) in HFinY.
  assert (HZY : fe_at my b 80 (point_field_limbs fz)).
  { exact (point_write_preserves_field mx my m0 bd bw bi b PointY PointZ (point_field_limbs fz)
      ltac:(discriminate) eq_refl HZX HFreeY HS HFrameY). }
  assert (HIZ : invA m0 bd dbase bw edge cursor N bi rc true (outX++outY) 256 (point_field_rho fz rc) [] my).
  { change (Int64.repr rc = Int64.repr rc /\
      finv m0 bd dbase bw edge cursor N bi my true ((outX++outY)++[]) /\
      Z.of_nat (length (outX++outY))+256 <= N /\ 0<=256).
    rewrite app_nil_r, app_length, HLX, HLY.
    split; [reflexivity|]; split; [exact HFinY|]; split; lia. }
  destruct (eval_point_bounded_field_write m0 bd dbase bw edge cursor N bi rc fz true (outX++outY)
    PointZ my b HO HBZ HZY HFreeY HS HIZ) as (mf & HCZ & HFinZ & HFreeZ & HFrameZ).
  exists mx,my,mf; split; [exact HCX|]; split; [exact HCY|]; split; [exact HCZ|].
  split; [exact HFinZ|]; split; [exact HFreeZ|].
  eapply lframe_trans; [eapply point_write_outside_point;exact HFrameX|].
  eapply lframe_trans; eapply point_write_outside_point; eassumption.
Qed.

Theorem eval_write_gej_general m0 bd dbase bw edge cursor N bi (rc : Z) m b fx fy fz :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  point_field_bounds fx -> point_field_bounds fy -> point_field_bounds fz ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  fe_at m b 80 (point_field_limbs fz) ->
  Mem.range_perm m b 0 128 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_gej)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      ((Simplicity.Translate.encode (point_field_output fx) ++
        Simplicity.Translate.encode (point_field_output fy)) ++
        Simplicity.Translate.encode (point_field_output fz)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HBX HBY HBZ HX HY HZ HP HS.
  destruct (eval_point_three_general_writes m0 bd dbase bw edge cursor N bi rc m b fx fy fz
    HO HN HI HBX HBY HBZ HX HY HZ HP HS) as (mx & my & mf & HCX & HCY & HCZ & HFin & HFree & HFrame).
  exists mf; split; [eapply eval_write_gej_from_calls;eassumption|].
  split; [exact HFin|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_write_gej_general.
