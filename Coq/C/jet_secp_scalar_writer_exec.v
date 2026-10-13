(** Whole unchanged scalar serializer: actual entry, helper calls and local
    buffer return/free are obtained from the checked symbolic execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_orc.
Require Import C.jet_sx_mem.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_encoding C.jet_output_layout C.jet_frame_bits.
Require Import Simplicity.BitMachine.
Require Import C.jet_secp_scalar_writer_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_writer_events bd dbase bi edge ibits rho layout :
  solves (evokA bd dbase bi edge ibits) rho
    (slog (fst (rsel rho layout (scalar_writer_result bd (Ptrofs.repr dbase))))).
Proof. constructor; [reflexivity|constructor]. Qed.

Section WRITE_FRAME.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (w0 : bool) (outs0 : list Cell).
Hypothesis HF0 : write_frame_at m0 bd dbase bw outedge cursor N.
Local Definition scalar_write_evok := evokA bd dbase bi edge ibits.
Local Definition scalar_write_inv := invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 256.
Local Definition scalar_write_ext := extA m0 bd bw bi.

Local Opaque secp_ge xfun scalar_writer_tree scalar_writer_result.
Theorem eval_write_scalar_from_initial_regions m layout rho :
  rep rho layout scalar_writer_initial_regs m ->
  xsep scalar_write_ext layout -> scalar_write_inv rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_scalar)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep rho layout scalar_writer_initial_regs mf /\
    scalar_write_inv rho
      (slog (fst (rsel rho (lay layout) (scalar_writer_result bd (Ptrofs.repr dbase))))) mf /\
    lframe (frame scalar_write_ext layout scalar_writer_initial_regs m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] write_fe_table scalar_write_evok scalar_write_inv scalar_write_ext)
    with (n := 600%nat) (fd := f_write_scalar) (xs := [XA bd (Ptrofs.repr dbase); XP 0 0])
      (regs := scalar_writer_initial_regs) (log := @nil event) (nv := 4%nat)
      (rr := scalar_writer_result bd (Ptrofs.repr dbase)) (ρ := rho) (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HF0.
  - apply invA_valid.
  - apply (write_fe_entries m0 bd dbase bw outedge cursor N bi edge rc ibits w0 outs0 HF0).
  - change (scalar_writer_run bd (Ptrofs.repr dbase) = Some (scalar_writer_result bd (Ptrofs.repr dbase))).
    exact (scalar_writer_run_eq bd (Ptrofs.repr dbase)).
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - apply scalar_writer_events.
  - rewrite scalar_writer_return in HReturn; subst result.
    rewrite scalar_writer_regions in HFinal.
    change (map (den rho (lay layout)) [XA bd (Ptrofs.repr dbase); XP 0 0]) with
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HExec.
    rewrite Z.add_0_r in HExec.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End WRITE_FRAME.
