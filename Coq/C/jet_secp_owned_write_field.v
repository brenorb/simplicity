(** Original field writer from actual enclosing ownership; no fixed point size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_field.
Require Import C.jet_secp_owned_field_slice C.jet_secp_owned_write_run C.jet_secp_owned_write_exec.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma owned_write_initial_rep size k t0 t1 t2 t3 t4 rc m b :
  point_coordinate_offset k + 40 <= size ->
  fe_at m b (point_coordinate_offset k) [t0;t1;t2;t3;t4] ->
  Mem.range_perm m b 0 size Cur Freeable ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) [(b,0)] (owned_write_initial_regs size k) m.
Proof.
  unfold owned_write_initial_regs. apply owned_field_slice_initial_rep.
Qed.

Theorem eval_owned_bounded_field_write size m0 bd dbase bw edge cursor N bi rc
    f w0 outs0 k m b :
  point_coordinate_offset k + 40 <= size ->
  write_frame_at m0 bd dbase bw edge cursor N ->
  point_field_bounds f ->
  fe_at m b (point_coordinate_offset k) (point_field_limbs f) ->
  Mem.range_perm m b 0 size Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 (point_field_rho f rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (point_field_output f)) /\
    Mem.range_perm mf b 0 size Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(b,0)] (owned_write_initial_regs size k) m) m mf.
Proof.
  intros HFit HO (H0&H1&H2&H3&H4) HField HFree HS HI.
  exact (eval_owned_wide_write_fe size m0 bd dbase bw edge cursor N bi rc
    (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f) w0 outs0 k m b
    HO H0 H1 H2 H3 H4
    (owned_write_initial_rep size k (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f)
      rc m b HFit HField HFree) HS HI).
Qed.
Print Assumptions owned_write_initial_rep.
Print Assumptions eval_owned_bounded_field_write.
