(** Execution of original field writer preserving the actual enclosing size. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_orc.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_encoding.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_local_regions.
Require Import C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_owned_write_run.
Require Import C.jet_secp_point_write_run.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge xfun owned_write_tree owned_write_result.

Theorem eval_owned_write_fe size m0 bd dbase bw edge cursor N bi rc w0 outs0 k m layout rho :
  write_frame_at m0 bd dbase bw edge cursor N ->
  rep rho layout (owned_write_initial_regs size k) m ->
  xsep (extA m0 bd bw bi) layout ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k))] E0 mf Vundef /\
    rep rho layout
      (sregs (fst (rsel rho (lay layout) (owned_write_result size k bd (Ptrofs.repr dbase))))) mf /\
    invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 rho
      (slog (fst (rsel rho (lay layout) (owned_write_result size k bd (Ptrofs.repr dbase))))) mf /\
    lframe (frame (extA m0 bd bw bi) layout (owned_write_initial_regs size k) m) m mf.
Proof.
  intros HO HR HS HI.
  destruct (xfun_top_sound secp_ge [] write_fe_table
    (evokA bd dbase bi edge [])
    (invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256) (extA m0 bd bw bi))
    with (n := 400%nat) (fd := f_write_fe)
      (xs := [XA bd (Ptrofs.repr dbase); XP 0 (point_coordinate_offset k)])
      (regs := owned_write_initial_regs size k) (log := @nil event) (nv := 6%nat)
      (rr := owned_write_result size k bd (Ptrofs.repr dbase)) (ρ := rho) (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HInv HFrame]]]]]]].
  - apply invA_stable; exact HO.
  - apply invA_valid.
  - eapply write_fe_entries; exact HO.
  - apply owned_write_run_eq.
  - exact HR.
  - split; intros id r ty HImpossible; discriminate.
  - exact HS.
  - exact HI.
  - rewrite owned_write_selected_log. apply write_fe_events.
  - rewrite owned_write_selected_return in HReturn; subst result.
    change (map (den rho (lay layout))
      [XA bd (Ptrofs.repr dbase); XP 0 (point_coordinate_offset k)]) with
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k))] in HExec.
    exists mf; split; [exact HExec|]. split; [exact HFinal|]. split; assumption.
Qed.

Theorem eval_owned_wide_write_fe size m0 bd dbase bw edge cursor N bi rc
    t0 t1 t2 t3 t4 w0 outs0 k m b :
  write_frame_at m0 bd dbase bw edge cursor N ->
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 -> Int64.unsigned t4 <= 2 ^ 60 ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) [(b,0)] (owned_write_initial_regs size k) m ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256
    (wide_fe_rho t0 t1 t2 t3 t4 rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (wide_fe_output t0 t1 t2 t3 t4)) /\
    Mem.range_perm mf b 0 size Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(b,0)] (owned_write_initial_regs size k) m) m mf.
Proof.
  intros HO H0 H1 H2 H3 H4 HR HS HI.
  destruct (eval_owned_write_fe size m0 bd dbase bw edge cursor N bi rc w0 outs0 k m [(b,0)]
    (wide_fe_rho t0 t1 t2 t3 t4 rc) HO HR HS HI)
    as (mf & HCall & HRep & HInv & HFrame).
  exists mf; split; [exact HCall|]. split.
  - unfold invA in HInv. rewrite owned_write_selected_log,
      write_fe_has_written, orb_true_r in HInv.
    rewrite wide_write_selected_outs in HInv by assumption. exact (proj1 (proj2 HInv)).
  - split; [|exact HFrame].
    destruct (owned_write_selected_storage size k bd (Ptrofs.repr dbase)
      (wide_fe_rho t0 t1 t2 t3 t4 rc) (lay [(b,0)])) as [HL HF].
    destruct (rep_free_region _ [(b,0)] _ mf 0 size HRep ltac:(rewrite HL;lia) HF)
      as [_ HFree]; exact HFree.
Qed.
Print Assumptions eval_owned_wide_write_fe.
