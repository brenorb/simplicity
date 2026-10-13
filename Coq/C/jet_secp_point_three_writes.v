(** Derive all three original field writes and literal point output from initial state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_encoding.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_initial.
Require Import C.jet_secp_point_write_preservation C.jet_secp_literal_infinity.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_zero256 literal_gej_infinity Simplicity.Translate.encode.

Lemma point_write_outside_point m mf m0 bd bw bi b k :
  lframe (frame (extA m0 bd bw bi) [(b,0)] (point_write_initial_regs k) m) m mf ->
  lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intro HF; eapply lframe_implies; [exact HF|].
  intros bx pos [HB HE] HV. unfold frame; split; [exact HV|]. split; [|exact HE].
  intro HFoot; apply HB; exact (proj1 (point_write_foot_bounds k b bx pos HFoot)).
Qed.

Theorem eval_point_three_zero_writes m0 bd dbase bw edge cursor N bi (rc : Z) m b :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  fe_at m b 0 (repeat Int64.zero 5) ->
  fe_at m b 40 (repeat Int64.zero 5) ->
  fe_at m b 80 (repeat Int64.zero 5) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mx my mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr 0)] E0 mx Vundef /\
    Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr 40)] E0 my Vundef /\
    Clight2.eval_funcall secp_ge my (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr 80)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_infinity Simplicity.Alg.CoreFunSem tt)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HX HY HZ HFree HS.
  set (rho := wide_fe_rho Int64.zero Int64.zero Int64.zero Int64.zero Int64.zero rc).
  set (out := Simplicity.Translate.encode (@literal_fe_zero256 Simplicity.Alg.CoreFunSem tt)).
  assert (HLen : length out = 256%nat).
  { unfold out; rewrite Simplicity.Translate.encode_length; reflexivity. }
  assert (HIX : invA m0 bd dbase bw edge cursor N bi rc false [] 256 rho [] m).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi m false [] /\
      0 + 256 <= N /\ 0 <= 256).
    split; [reflexivity|]. split; [exact HI|]. split; lia. }
  destruct (eval_point_write_from_owned_field m0 bd dbase bw edge cursor N bi rc
    Int64.zero Int64.zero Int64.zero Int64.zero Int64.zero false [] PointX m b HO
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) HX HFree HS HIX)
    as (mx & HCallX & HFinX & HFreeX & HFrameX).
  rewrite zero_field_writer_literal_output in HFinX.
  change (finv m0 bd dbase bw edge cursor N bi mx true out) in HFinX.
  assert (HYX : fe_at mx b 40 (repeat Int64.zero 5)).
  { exact (point_write_preserves_zero_field m mx m0 bd bw bi b PointX PointY
      ltac:(discriminate) HY HFreeX HS HFrameX). }
  assert (HZX : fe_at mx b 80 (repeat Int64.zero 5)).
  { exact (point_write_preserves_zero_field m mx m0 bd bw bi b PointX PointZ
      ltac:(discriminate) HZ HFreeX HS HFrameX). }
  assert (HIY : invA m0 bd dbase bw edge cursor N bi rc true out 256 rho [] mx).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi mx true (out ++ []) /\
      Z.of_nat (length out) + 256 <= N /\ 0 <= 256).
    rewrite app_nil_r, HLen. split; [reflexivity|]. split; [exact HFinX|]. split; lia. }
  destruct (eval_point_write_from_owned_field m0 bd dbase bw edge cursor N bi rc
    Int64.zero Int64.zero Int64.zero Int64.zero Int64.zero true out PointY mx b HO
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) HYX HFreeX HS HIY)
    as (my & HCallY & HFinY & HFreeY & HFrameY).
  rewrite zero_field_writer_literal_output in HFinY.
  change (finv m0 bd dbase bw edge cursor N bi my true (out ++ out)) in HFinY.
  assert (HZY : fe_at my b 80 (repeat Int64.zero 5)).
  { exact (point_write_preserves_zero_field mx my m0 bd bw bi b PointY PointZ
      ltac:(discriminate) HZX HFreeY HS HFrameY). }
  assert (HIZ : invA m0 bd dbase bw edge cursor N bi rc true (out ++ out) 256 rho [] my).
  { change (Int64.repr rc = Int64.repr rc /\ finv m0 bd dbase bw edge cursor N bi my true ((out ++ out) ++ []) /\
      Z.of_nat (length (out ++ out)) + 256 <= N /\ 0 <= 256).
    rewrite app_nil_r, app_length, HLen. split; [reflexivity|]. split; [exact HFinY|]. split; lia. }
  destruct (eval_point_write_from_owned_field m0 bd dbase bw edge cursor N bi rc
    Int64.zero Int64.zero Int64.zero Int64.zero Int64.zero true (out ++ out) PointZ my b HO
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) ltac:(change (0 <= 2^60);lia)
    ltac:(change (0 <= 2^60);lia) HZY HFreeY HS HIZ)
    as (mf & HCallZ & HFinZ & HFreeZ & HFrameZ).
  rewrite zero_field_writer_literal_output in HFinZ.
  change (finv m0 bd dbase bw edge cursor N bi mf true ((out ++ out) ++ out)) in HFinZ.
  exists mx, my, mf. split; [exact HCallX|]. split; [exact HCallY|]. split; [exact HCallZ|].
  split.
  - rewrite literal_gej_infinity_encoding; exact HFinZ.
  - split; [exact HFreeZ|].
    eapply lframe_trans; [eapply point_write_outside_point; exact HFrameX|].
    eapply lframe_trans; eapply point_write_outside_point; eassumption.
Qed.
Print Assumptions eval_point_three_zero_writes.
