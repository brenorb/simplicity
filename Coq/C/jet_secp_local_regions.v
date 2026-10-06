(** The original wrappers with the public caller's local regions marked
    Freeable. This metadata changes proof invariants, never C or Clight code. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wrapper_run C.jet_secp_read_fe_numeric.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_write_fe_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition free_region (reg : region) (sz : Z) : region := mkreg (rcells reg) (rw reg) (Some sz).
Definition local_read_initial_regs bi edge :=
  [free_region fe_undef 40;
   free_region (mkreg (mk_frame_cells (XA bi edge) Int64.zero) true None) 16].
Definition local_read_run bi edge : option res :=
  xfun (genv_cenv secp_ge) [] read_fe_table 400 f_read_fe
    [XP 0 0; XP 1 0] (local_read_initial_regs bi edge) [] 1.
Definition local_read_tree := Eval vm_compute in fun bi edge => local_read_run bi edge.
Definition local_read_result bi edge : res :=
  match local_read_tree bi edge with Some rr => rr | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal end.
Lemma local_read_run_eq bi edge : local_read_run bi edge = Some (local_read_result bi edge).
Proof. reflexivity. Qed.
Definition local_write_initial_regs := [free_region (fe_reg (vars5 1)) 40].
Definition local_write_run bd base : option res :=
  xfun (genv_cenv secp_ge) [] write_fe_table 400 f_write_fe
    [XA bd base; XP 0 0] local_write_initial_regs [] 6.
Definition local_write_tree := Eval vm_compute in fun bd base => local_write_run bd base.
Definition local_write_result bd base : res :=
  match local_write_tree bd base with Some rr => rr | None => RDone (mkst (PTree.empty sx) [] [] 0) ONormal end.
Lemma local_write_run_eq bd base : local_write_run bd base = Some (local_write_result bd base).
Proof. reflexivity. Qed.
Lemma local_read_selected_cells rho layout bi edge :
  cells0 (fst (rsel rho layout (local_read_result bi edge))) =
    cells0 (fst (rsel rho layout (read_fe_result bi edge))).
Proof. rewrite !selected_cells_rsel; reflexivity. Qed.
Lemma local_read_selected_log rho layout bi edge :
  slog (fst (rsel rho layout (local_read_result bi edge))) = read_fe_log bi edge.
Proof. apply all_leaf_logs_selected; split; [split; reflexivity|reflexivity]. Qed.
Lemma local_write_selected_log rho layout bd base :
  slog (fst (rsel rho layout (local_write_result bd base))) =
    slog (fst (rsel rho layout (write_fe_result bd base))).
Proof. rewrite !selected_events_rsel; reflexivity. Qed.
Fixpoint all_leaf_property (P : sstate -> Prop) rr : Prop :=
  match rr with RDone state _ => P state | RIf _ a b => all_leaf_property P a /\ all_leaf_property P b end.
Lemma all_leaf_property_selected P rr :
  all_leaf_property P rr -> forall rho layout, P (fst (rsel rho layout rr)).
Proof.
  induction rr as [state outcome|condition a IHa b IHb]; cbn [all_leaf_property rsel].
  - intros H rho layout; exact H.
  - intros [HA HB] rho layout; destruct (truth rho layout condition); auto.
Qed.
Definition local_read_storage_shape state : Prop :=
  length (sregs state) = 2%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some 40 /\
  rfree (nth 1 (sregs state) (mkreg [] true None)) = Some 16.
Lemma local_read_leaf_storage bi edge : all_leaf_property local_read_storage_shape (local_read_result bi edge).
Proof. split; [split; repeat split; reflexivity|repeat split; reflexivity]. Qed.
Lemma local_read_selected_storage rho layout bi edge :
  local_read_storage_shape (fst (rsel rho layout (local_read_result bi edge))).
Proof. apply all_leaf_property_selected; apply local_read_leaf_storage. Qed.
Definition local_write_storage_shape state : Prop :=
  length (sregs state) = 1%nat /\
  rfree (nth 0 (sregs state) (mkreg [] true None)) = Some 40.
Lemma local_write_leaf_storage bd base : all_leaf_property local_write_storage_shape (local_write_result bd base).
Proof. split; split; reflexivity. Qed.
Lemma local_write_selected_storage rho layout bd base :
  local_write_storage_shape (fst (rsel rho layout (local_write_result bd base))).
Proof. apply all_leaf_property_selected; apply local_write_leaf_storage. Qed.
Lemma rep_free_region rho layout regs m r sz :
  rep rho layout regs m ->
  (r < length regs)%nat -> rfree (nth r regs (mkreg [] true None)) = Some sz ->
  bas layout r = 0 /\ Mem.range_perm m (blk layout r) 0 sz Cur Freeable.
Proof.
  intros HRep HIndex HFree.
  pose proof (nth_error_nth' regs (mkreg [] true None) HIndex) as HNth.
  destruct (rep_region _ _ _ _ _ _ HRep HNth) as (_ & _ & _ & _ & HStorage).
  rewrite HFree in HStorage; destruct HStorage as [HBase [_ [HRange _]]].
  split; [exact HBase|exact HRange].
Qed.

Lemma local_read_selected_return rho layout bi edge :
  (stemps (fst (rsel rho layout (local_read_result bi edge))))!1%positive = None.
Proof.
  apply all_leaf_property_selected with
    (P := fun state => (stemps state)!1%positive = None).
  split; [split; reflexivity|reflexivity].
Qed.
Lemma local_write_selected_return rho layout bd base :
  (stemps (fst (rsel rho layout (local_write_result bd base))))!1%positive = None.
Proof.
  apply all_leaf_property_selected with
    (P := fun state => (stemps state)!1%positive = None).
  split; reflexivity.
Qed.

Require Import C.jet_encoding C.jet_output_layout C.jet_frame_layout.
Require Simplicity.BitMachine.
Section LOCAL_READ.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (outs0 : list Simplicity.BitMachine.Cell) (cap : Z).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Hypothesis HInput : frame_input_cells_at m0 bi edge rc (map Some ibits).
Hypothesis HCursor : 0 <= rc.
Hypothesis HCursorMax : rc + Z.of_nat (length ibits) <= Int64.max_unsigned.
Hypothesis HLength : length ibits = 256%nat.
Local Definition rd_ev := evokA bd dbase bi edge ibits.
Local Definition rd_inv := invA m0 bd dbase bw outedge cursor N bi rc false outs0 cap.
Local Definition rd_ext := extA m0 bd bw bi.
Local Opaque secp_ge xfun local_read_tree local_read_result.
Theorem eval_local_read_fe m layout :
  rep (read_fe_rho ibits rc) layout (local_read_initial_regs bi (Ptrofs.repr edge)) m ->
  xsep rd_ext layout -> rd_inv (read_fe_rho ibits rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef /\
    rep (read_fe_rho ibits rc) layout
      (sregs (fst (rsel (read_fe_rho ibits rc) (lay layout)
        (local_read_result bi (Ptrofs.repr edge))))) mf /\
    rd_inv (read_fe_rho ibits rc) (read_fe_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame rd_ext layout (local_read_initial_regs bi (Ptrofs.repr edge)) m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] read_fe_table rd_ev rd_inv rd_ext)
    with (n := 400%nat) (fd := f_read_fe) (xs := [XP 0 0; XP 1 0])
      (regs := local_read_initial_regs bi (Ptrofs.repr edge)) (log := @nil event) (nv := 1%nat)
      (rr := local_read_result bi (Ptrofs.repr edge)) (ρ := read_fe_rho ibits rc)
      (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HOutput.
  - apply invA_valid.
  - eapply read_fe_entries; eassumption.
  - apply local_read_run_eq.
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - rewrite local_read_selected_log.
    rewrite <- (read_fe_selected_log bi (Ptrofs.repr edge) (read_fe_rho ibits rc) (lay layout)).
    apply read_fe_input_events.
  - rewrite local_read_selected_return in HReturn; subst result.
    change (map (den (read_fe_rho ibits rc) (lay layout)) [XP 0 0; XP 1 0]) with
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
       Vptr (blk layout 1) (Ptrofs.repr (bas layout 1 + 0))] in HExec.
    rewrite !Z.add_0_r in HExec; rewrite local_read_selected_log in HFinalInv.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End LOCAL_READ.

Section LOCAL_WRITE.
Variables (m0 : Mem.mem) (bd : block) (dbase : Z) (bw : block)
  (outedge cursor N : Z) (bi : block) (edge rc : Z) (ibits : list bool)
  (w0 : bool) (outs0 : list Simplicity.BitMachine.Cell).
Hypothesis HOutput : write_frame_at m0 bd dbase bw outedge cursor N.
Local Definition wr_ev := evokA bd dbase bi edge ibits.
Local Definition wr_inv := invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 256.
Local Definition wr_ext := extA m0 bd bw bi.
Local Opaque secp_ge xfun local_write_tree local_write_result.
Theorem eval_local_write_fe m layout rho :
  rep rho layout local_write_initial_regs m ->
  xsep wr_ext layout -> wr_inv rho [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep rho layout
      (sregs (fst (rsel rho (lay layout) (local_write_result bd (Ptrofs.repr dbase))))) mf /\
    wr_inv rho
      (slog (fst (rsel rho (lay layout) (local_write_result bd (Ptrofs.repr dbase))))) mf /\
    lframe (frame wr_ext layout local_write_initial_regs m) m mf.
Proof.
  intros HRep HSep HInv.
  destruct (xfun_top_sound secp_ge [] write_fe_table wr_ev wr_inv wr_ext)
    with (n := 400%nat) (fd := f_write_fe) (xs := [XA bd (Ptrofs.repr dbase); XP 0 0])
      (regs := local_write_initial_regs) (log := @nil event) (nv := 6%nat)
      (rr := local_write_result bd (Ptrofs.repr dbase)) (ρ := rho) (β := layout) (m := m)
    as [mf [result [HExec [HFinal [HReturn [HShape [HFinalInv HFrame]]]]]]].
  - apply invA_stable; exact HOutput.
  - apply invA_valid.
  - eapply write_fe_entries; exact HOutput.
  - apply local_write_run_eq.
  - exact HRep.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - rewrite local_write_selected_log; apply write_fe_events.
  - rewrite local_write_selected_return in HReturn; subst result.
    change (map (den rho (lay layout)) [XA bd (Ptrofs.repr dbase); XP 0 0]) with
      [Vptr bd (Ptrofs.repr dbase); Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HExec.
    rewrite Z.add_0_r in HExec.
    exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; assumption.
Qed.
End LOCAL_WRITE.

Require Import C.jet_secp_b32_exec C.jet_secp_wrapper_storage.
Lemma region_with_freeable rho layout m r reg sz :
  region_ok rho layout m r reg -> bas layout r = 0 -> rw reg = true ->
  Mem.range_perm m (blk layout r) 0 sz Cur Freeable ->
  Forall (fun c => cofs c + size_chunk (cchunk c) <= sz) (rcells reg) ->
  region_ok rho layout m r (free_region reg sz).
Proof.
  intros (HBase & HValid & HSorted & HCells & _) HZero HWrite HFree HSize.
  unfold free_region, region_ok; cbn [rw rcells rfree].
  split; [exact HBase|]; split; [exact HValid|]; split; [exact HSorted|]; split; [exact HCells|].
  split; [exact HZero|]; split; [exact HWrite|]; split; assumption.
Qed.
Lemma freeable_range_writable m b lo hi :
  Mem.range_perm m b lo hi Cur Freeable -> Mem.range_perm m b lo hi Cur Writable.
Proof. intros H pos HRange; eapply Mem.perm_implies; [apply H; exact HRange|constructor]. Qed.
Lemma fe_undef_storage_size :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 40) (rcells fe_undef).
Proof. repeat constructor; cbn; lia. Qed.
Lemma frame_cells_storage_size bi edge :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 16)
    (mk_frame_cells (XA bi edge) Int64.zero).
Proof. repeat constructor; cbn; lia. Qed.
Lemma field_cells_storage_size :
  Forall (fun c => cofs c + size_chunk (cchunk c) <= 40) (rcells (fe_reg (vars5 1))).
Proof. repeat constructor; cbn; lia. Qed.
Theorem local_read_initial_rep_from_storage bits rc m ba bl bi edge :
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  rep (read_fe_rho bits rc) [(ba, 0); (bl, 0)] (local_read_initial_regs bi (Ptrofs.repr edge)) m.
Proof.
  intros HFieldFree HFrameFree HFrame HSeparate.
  apply two_region_rep_separate; [reflexivity|exact HSeparate| |].
  - apply region_with_freeable.
    + apply region_fe_undefined_from_storage; cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0; reflexivity.
      * change (40 <= 18446744073709551615); lia.
      * apply freeable_range_writable; exact HFieldFree.
    + reflexivity.
    + reflexivity.
    + exact HFieldFree.
    + apply fe_undef_storage_size.
  - apply region_with_freeable.
    + apply read_fe_region_from_frame; cbn [bas blk lay nth fst snd].
      * lia.
      * exists 0; reflexivity.
      * change (16 <= 18446744073709551615); lia.
      * apply freeable_range_writable; exact HFrameFree.
      * exact HFrame.
    + reflexivity.
    + reflexivity.
    + exact HFrameFree.
    + apply frame_cells_storage_size.
Qed.
Theorem local_write_initial_rep_from_field value rc m ba :
  fe_at m ba 0 (map Int64.repr (C.jet_secp_fe_math.fe_limbs_of value)) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  rep (write_fe_rho value rc) [(ba, 0)] local_write_initial_regs m.
Proof.
  intros HField HFree.
  apply (rep_add _ [] [] m ba 0); [apply rep_nil|cbn; tauto|].
  apply region_with_freeable.
  - apply write_fe_region_from_field; exact HField.
  - reflexivity.
  - reflexivity.
  - exact HFree.
  - apply field_cells_storage_size.
Qed.
