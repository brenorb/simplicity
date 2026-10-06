From Coq Require Import ZArith List Bool Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_orc C.jet_sx_rep C.jet_sx_pure.
Require Import C.jet_secp_frame C.jet_secp_fe_b32.
Require Import C.jet_sx_mem C.jet_encoding C.jet_output_layout C.jet_frame_bits.
Require Import Simplicity.BitMachine.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition read_fe_table : list (ident * fentry) :=
  (C.jets._read8s, FOra C.jets.f_read8s (orc_rd8 false 256)) :: int_table secp_pure.
Definition read_fe_initial_regs (input_edge : block) (edge : ptrofs) : list region :=
  [fe_undef; mkreg (mk_frame_cells (XA input_edge edge) Int64.zero) true None].
Definition read_fe_run (input_edge : block) (edge : ptrofs) : option res :=
  xfun (genv_cenv secp_ge) [] read_fe_table 400 f_read_fe
    [XP 0 0; XP 1 0] (read_fe_initial_regs input_edge edge) [] 1.
Definition read_fe_tree := Eval vm_compute in fun input_edge edge => read_fe_run input_edge edge.
Lemma read_fe_tree_nonempty input_edge edge :
  match read_fe_tree input_edge edge with Some _ => true | None => false end = true.
Proof. reflexivity. Qed.
Fixpoint branch_count (r : res) : nat :=
  match r with RDone _ _ => 1%nat | RIf _ a b => branch_count a + branch_count b end.

Definition read_fe_result input_edge edge : res :=
  match read_fe_tree input_edge edge with
  | Some rr => rr
  | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal
  end.
Lemma read_fe_run_eq input_edge edge :
  read_fe_run input_edge edge = Some (read_fe_result input_edge edge).
Proof. reflexivity. Qed.

Fixpoint all_leaf_logs (log : list event) (rr : res) : Prop :=
  match rr with
  | RDone state _ => slog state = log
  | RIf _ a b => all_leaf_logs log a /\ all_leaf_logs log b
  end.
Lemma all_leaf_logs_selected log rr :
  all_leaf_logs log rr -> forall rho layout, slog (fst (rsel rho layout rr)) = log.
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn.
  - intros H rho layout; exact H.
  - intros [HA HB] rho layout; destruct (truth rho layout condition); auto.
Qed.
Definition read_fe_log input_edge edge : list event :=
  [mkev tRD8 1 32 [XA input_edge edge; XLc Int64.zero; XLc (Int64.repr 32)]].
Lemma read_fe_result_leaf_logs input_edge edge :
  all_leaf_logs (read_fe_log input_edge edge) (read_fe_result input_edge edge).
Proof. split; [split; reflexivity|reflexivity]. Qed.
Lemma read_fe_selected_log input_edge edge rho layout :
  slog (fst (rsel rho layout (read_fe_result input_edge edge))) = read_fe_log input_edge edge.
Proof. apply all_leaf_logs_selected; apply read_fe_result_leaf_logs. Qed.

Lemma read_fe_selected_return input_edge edge rho layout :
  (stemps (fst (rsel rho layout (read_fe_result input_edge edge))))!1%positive = None.
Proof.
  cbn [read_fe_result read_fe_tree rsel fst stemps].
  repeat match goal with |- context[if ?condition then _ else _] => destruct condition end;
    reflexivity.
Qed.

Definition read_fe_rho (ibits : list bool) (rc : Z) (n : nat) : int64 :=
  match n with
  | 0%nat => Int64.repr rc
  | S j => Int64.repr (ifield ibits (8 * j) 8)
  end.

Section READ_FRAME.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Cell) (cap : Z).
Hypothesis HF0 : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HLength : length ibits = 256%nat.

Local Definition read_evok := evokA bd dbase bi edge ibits.
Local Definition read_inv := invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap.
Local Definition read_ext := extA m0 bd bw bi.

Lemma read_fe_entries id ent :
  flookup read_fe_table id = Some ent ->
  (exists b, Genv.find_symbol secp_ge id = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True | FOra fd oracle => oracle_ok secp_ge read_evok read_inv read_ext fd oracle end.
Proof.
  cbn [read_fe_table flookup].
  destruct (Pos.eqb C.jets._read8s id) eqn:HId.
  - apply Pos.eqb_eq in HId; subst id; intros HEnt; inversion HEnt; subst ent.
    split.
    + destruct (secp_core_helpers_entries C.jets._read8s C.jets.f_read8s)
        as [b1 [b2 [H1 [H2 [H3 H4]]]]].
      { unfold secp_core_helpers; do 19 right; left; reflexivity. }
      exists b2; split; assumption.
    + apply orc_rd8_ok; try assumption; rewrite HLength; reflexivity.
  - intro HEnt; destruct (int_table_lookup _ _ _ HEnt) as [fd [HEntry HIn]].
    rewrite HEntry; split; [apply secp_pure_ok; exact HIn|exact I].
Qed.

Lemma read_fe_input_events layout :
  solves read_evok (read_fe_rho ibits rc)
    (slog (fst (rsel (read_fe_rho ibits rc) (lay layout)
      (read_fe_result bi (Ptrofs.repr edge))))).
Proof.
  rewrite read_fe_selected_log; unfold solves; constructor; [|constructor].
  unfold read_evok, evokA, read_fe_log; cbn [etag eargs ecnt ebase den].
  split; [reflexivity|].
  intros j HJ; change ((1 + j)%nat) with (S j).
  unfold read_fe_rho; change (Int64.unsigned Int64.zero) with 0.
  cbn [Z.to_nat]; reflexivity.
Qed.
Local Opaque secp_ge xfun read_fe_tree read_fe_result.

Theorem eval_read_fe_from_initial_regions m layout :
  rep (read_fe_rho ibits rc) layout (read_fe_initial_regs bi (Ptrofs.repr edge)) m ->
  xsep read_ext layout ->
  read_inv (read_fe_rho ibits rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep (read_fe_rho ibits rc) layout
      (sregs (fst (rsel (read_fe_rho ibits rc) (lay layout)
        (read_fe_result bi (Ptrofs.repr edge))))) mf /\
    read_inv (read_fe_rho ibits rc) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame read_ext layout (read_fe_initial_regs bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] read_fe_table read_evok read_inv read_ext)
    with (n := 400%nat) (fd := f_read_fe) (xs := [XP 0 0; XP 1 0])
      (regs := read_fe_initial_regs bi (Ptrofs.repr edge)) (log := @nil event) (nv := 1%nat)
      (rr := read_fe_result bi (Ptrofs.repr edge)) (ρ := read_fe_rho ibits rc)
      (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HF0.
  - apply invA_valid.
  - apply read_fe_entries.
  - change (read_fe_run bi (Ptrofs.repr edge) = Some (read_fe_result bi (Ptrofs.repr edge))).
    exact (read_fe_run_eq bi (Ptrofs.repr edge)).
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - apply read_fe_input_events.
  - rewrite read_fe_selected_return in HReturn; subst result.
    change (map (den (read_fe_rho ibits rc) (lay layout)) [XP 0 0; XP 1 0]) with
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HExec.
    rewrite !Z.add_0_r in HExec; rewrite read_fe_selected_log in HFinalInv.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End READ_FRAME.
