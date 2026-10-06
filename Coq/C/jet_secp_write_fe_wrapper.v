From Coq Require Import ZArith List Bool Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_orc C.jet_sx_rep C.jet_sx_pure.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_sx_mem C.jet_encoding C.jet_output_layout C.jet_frame_bits.
Require Import Simplicity.BitMachine.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition write_fe_table : list (ident * fentry) :=
  (C.jets._write8s, FOra C.jets.f_write8s (orc_wr8 256)) :: int_table secp_pure.
Definition write_fe_initial_regs : list region := [fe_reg (vars5 1)].
Definition write_fe_run (output_frame : block) (base : ptrofs) : option res :=
  xfun (genv_cenv secp_ge) [] write_fe_table 400 f_write_fe
    [XA output_frame base; XP 0 0] write_fe_initial_regs [] 6.
Definition write_fe_tree := Eval vm_compute in fun output_frame base => write_fe_run output_frame base.
Lemma write_fe_tree_nonempty output_frame base :
  match write_fe_tree output_frame base with Some _ => true | None => false end = true.
Proof. reflexivity. Qed.
Definition write_fe_result output_frame base : res :=
  match write_fe_tree output_frame base with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.
Lemma write_fe_run_eq output_frame base :
  write_fe_run output_frame base = Some (write_fe_result output_frame base).
Proof. reflexivity. Qed.

Fixpoint all_leaf_event_contracts (contract : event -> Prop) (rr : res) : Prop :=
  match rr with
  | RDone state _ => Forall contract (slog state)
  | RIf _ a b => all_leaf_event_contracts contract a /\ all_leaf_event_contracts contract b
  end.
Lemma all_leaf_event_contracts_selected contract rr :
  all_leaf_event_contracts contract rr ->
  forall rho layout, Forall contract (slog (fst (rsel rho layout rr))).
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn.
  - intros H rho layout; exact H.
  - intros [HA HB] rho layout; destruct (truth rho layout condition); auto.
Qed.
Lemma write_fe_selected_return output_frame base rho layout :
  (stemps (fst (rsel rho layout (write_fe_result output_frame base))))!1%positive = None.
Proof.
  cbn [write_fe_result write_fe_tree rsel fst stemps].
  repeat match goal with |- context[if ?condition then _ else _] => destruct condition end;
    reflexivity.
Qed.
Lemma write_fe_leaf_events bd dbase bi edge ibits rho :
  all_leaf_event_contracts (evokA bd dbase bi edge ibits rho)
    (write_fe_result bd (Ptrofs.repr dbase)).
Proof.
  split.
  - constructor; [reflexivity|constructor].
  - constructor; [reflexivity|constructor].
Qed.

Section WRITE_FRAME.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (w0 : bool) (outs0 : list Cell).
Hypothesis HF0 : write_frame_at m0 bd dbase bw outedge cursor N.
Local Definition write_evok := evokA bd dbase bi edge ibits.
Local Definition write_inv := invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 256.
Local Definition write_ext := extA m0 bd bw bi.

Lemma write_fe_entries id ent :
  flookup write_fe_table id = Some ent ->
  (exists b, Genv.find_symbol secp_ge id = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True | FOra fd oracle => oracle_ok secp_ge write_evok write_inv write_ext fd oracle end.
Proof.
  cbn [write_fe_table flookup].
  destruct (Pos.eqb C.jets._write8s id) eqn:HId.
  - apply Pos.eqb_eq in HId; subst id; intros HEnt; inversion HEnt; subst ent.
    split.
    + destruct (secp_core_helpers_entries C.jets._write8s C.jets.f_write8s)
        as [b1 [b2 [H1 [H2 [H3 H4]]]]].
      { unfold secp_core_helpers; do 18 right; left; reflexivity. }
      exists b2; split; assumption.
    + apply orc_wr8_ok; exact HF0.
  - intro HEnt; destruct (int_table_lookup _ _ _ HEnt) as [fd [HEntry HIn]].
    rewrite HEntry; split; [apply secp_pure_ok; exact HIn|exact I].
Qed.

Lemma write_fe_events rho layout :
  solves write_evok rho
    (slog (fst (rsel rho (lay layout) (write_fe_result bd (Ptrofs.repr dbase))))).
Proof. apply all_leaf_event_contracts_selected; apply write_fe_leaf_events. Qed.

Local Opaque secp_ge xfun write_fe_tree write_fe_result.
Theorem eval_write_fe_from_initial_regions m layout rho :
  rep rho layout write_fe_initial_regs m ->
  xsep write_ext layout -> write_inv rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep rho layout
      (sregs (fst (rsel rho (lay layout) (write_fe_result bd (Ptrofs.repr dbase))))) mf /\
    write_inv rho
      (slog (fst (rsel rho (lay layout) (write_fe_result bd (Ptrofs.repr dbase))))) mf /\
    lframe (frame write_ext layout write_fe_initial_regs m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] write_fe_table write_evok write_inv write_ext)
    with (n := 400%nat) (fd := f_write_fe) (xs := [XA bd (Ptrofs.repr dbase); XP 0 0])
      (regs := write_fe_initial_regs) (log := @nil event) (nv := 6%nat)
      (rr := write_fe_result bd (Ptrofs.repr dbase)) (ρ := rho) (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HF0.
  - apply invA_valid.
  - apply write_fe_entries.
  - change (write_fe_run bd (Ptrofs.repr dbase) = Some (write_fe_result bd (Ptrofs.repr dbase))).
    exact (write_fe_run_eq bd (Ptrofs.repr dbase)).
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - apply write_fe_events.
  - rewrite write_fe_selected_return in HReturn; subst result.
    change (map (den rho (lay layout)) [XA bd (Ptrofs.repr dbase); XP 0 0]) with
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HExec.
    rewrite Z.add_0_r in HExec.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End WRITE_FRAME.
