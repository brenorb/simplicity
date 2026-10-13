(** Shared bounded-field interface for original point-coordinate writers. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_initial.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Record point_field := mkpointfield { pf0 : int64; pf1 : int64; pf2 : int64; pf3 : int64; pf4 : int64 }.
Definition point_field_limbs f := [pf0 f;pf1 f;pf2 f;pf3 f;pf4 f].
Definition point_field_bounds f :=
  Int64.unsigned (pf0 f) <= 2^60 /\ Int64.unsigned (pf1 f) <= 2^60 /\
  Int64.unsigned (pf2 f) <= 2^60 /\ Int64.unsigned (pf3 f) <= 2^60 /\ Int64.unsigned (pf4 f) <= 2^60.
Definition point_field_output f := wide_fe_output (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f).
Definition point_field_rho f rc := wide_fe_rho (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f) rc.

Theorem eval_point_bounded_field_write m0 bd dbase bw edge cursor N bi rc
    f w0 outs0 k m b :
  write_frame_at m0 bd dbase bw edge cursor N ->
  point_field_bounds f ->
  fe_at m b (point_coordinate_offset k) (point_field_limbs f) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 (point_field_rho f rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (point_field_output f)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(b,0)] (point_write_initial_regs k) m) m mf.
Proof.
  intros HO (H0&H1&H2&H3&H4) HField HFree HS HI.
  exact (eval_point_write_from_owned_field m0 bd dbase bw edge cursor N bi rc
    (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f) w0 outs0 k m b
    HO H0 H1 H2 H3 H4 HField HFree HS HI).
Qed.
Print Assumptions eval_point_bounded_field_write.
