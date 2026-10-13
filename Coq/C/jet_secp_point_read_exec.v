(** Actual original field reader on a slice of one owned Jacobian point.
    Initial symbolic representation is an intermediate contract, not the final jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import Simplicity.BitMachine.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run C.jet_secp_point_read_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Section POINT_READ.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Cell) (cap : Z).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HLength : length ibits = 256%nat.
Local Opaque secp_ge xfun point_read_tree point_read_result.

Theorem eval_point_read_fe k m layout :
  rep (read_fe_rho ibits rc) layout (point_read_initial_regs k bi (Ptrofs.repr edge)) m ->
  xsep (extA m0 bd bw bi) layout ->
  invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap (read_fe_rho ibits rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep (read_fe_rho ibits rc) layout
      (sregs (fst (rsel (read_fe_rho ibits rc) (lay layout)
        (point_read_result k bi (Ptrofs.repr edge))))) mf /\
    invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap
      (read_fe_rho ibits rc) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame (extA m0 bd bw bi) layout
      (point_read_initial_regs k bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] read_fe_table
    (evokA bd dbase bi edge ibits)
    (invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap)
    (extA m0 bd bw bi))
    with (n := 400%nat) (fd := f_read_fe)
      (xs := [XP 0 (point_coordinate_offset k); XP 1 0])
      (regs := point_read_initial_regs k bi (Ptrofs.repr edge))
      (log := @nil event) (nv := 1%nat)
      (rr := point_read_result k bi (Ptrofs.repr edge))
      (ρ := read_fe_rho ibits rc) (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HOutput.
  - apply invA_valid.
  - eapply read_fe_entries; eassumption.
  - apply point_read_run_eq.
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - rewrite point_read_selected_log.
    rewrite <- (read_fe_selected_log bi (Ptrofs.repr edge) (read_fe_rho ibits rc) (lay layout)).
    apply read_fe_input_events.
  - rewrite point_read_selected_return in HReturn; subst result.
    change (map (den (read_fe_rho ibits rc) (lay layout))
      [XP 0 (point_coordinate_offset k); XP 1 0]) with
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + point_coordinate_offset k));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HExec.
    rewrite Z.add_0_r in HExec.
    rewrite point_read_selected_log in HFinalInv.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End POINT_READ.
Print Assumptions eval_point_read_fe.
