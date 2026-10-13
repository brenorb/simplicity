(* Execute read_scalar's actual first call in its allocated buffer context.
   The original NULL-pointer setter call is handled separately, not rewritten. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_pure C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_b32 C.jet_secp_wrapper_run C.jet_secp_local_regions.
Require Import C.jet_encoding C.jet_output_layout C.jet_frame_bits.
Require Import C.jet_secp_shift64_executor C.jet_secp_shift64_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_reader_table :=
  (C.jets._read8s, FOra C.jets.f_read8s (orc_rd8 false 256)) :: secp_shift64_table.
Definition scalar_reader_initial_regs bi edge :=
  [mkreg [mkcell 0 Mint64 None; mkcell 8 Mint64 None;
          mkcell 16 Mint64 None; mkcell 24 Mint64 None] true (Some 32);
   mkreg (mk_frame_cells (XA bi edge) Int64.zero) true (Some 16)].
Definition scalar_reader_buffer := mkreg (byte_undef 0 32) true (Some 32).
Definition scalar_reader_venv := [(jets_secp._buf, (2%nat, tarray tuchar 32))].
Definition scalar_reader_temps :=
  PTree.set jets_secp._src (XP 1 0) (PTree.set jets_secp._r (XP 0 0) (PTree.empty sx)).
Definition scalar_reader_initial bi edge :=
  mkst scalar_reader_temps (scalar_reader_initial_regs bi edge ++ [scalar_reader_buffer]) [] 1.
Definition scalar_reader_first :=
  match fn_body f_read_scalar with Ssequence first _ => first | _ => Sskip end.
Definition scalar_reader_run bi edge :=
  xstmt (genv_cenv secp_ge) [] scalar_reader_table 1000 scalar_reader_venv
    (scalar_reader_initial bi edge) scalar_reader_first.
Definition scalar_reader_tree := Eval vm_compute in fun bi edge => scalar_reader_run bi edge.
Definition scalar_reader_state bi edge :=
  match scalar_reader_tree bi edge with Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_reader_run_eq bi edge :
  scalar_reader_run bi edge = Some (RDone (scalar_reader_state bi edge) ONormal).
Proof. reflexivity. Qed.
Lemma scalar_reader_return bi edge :
  stemps (scalar_reader_state bi edge) = scalar_reader_temps.
Proof. reflexivity. Qed.
Definition scalar_reader_log bi edge :=
  read_fe_log bi edge.
Lemma scalar_reader_log_eq bi edge :
  slog (scalar_reader_state bi edge) = scalar_reader_log bi edge.
Proof. reflexivity. Qed.
Lemma scalar_reader_allocation :
  xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
    (fn_vars f_read_scalar) 2 = Some ([scalar_reader_buffer], scalar_reader_venv).
Proof. reflexivity. Qed.
Lemma scalar_reader_read_regions bi edge :
  sregs (scalar_reader_state bi edge) =
    [nth 0 (scalar_reader_initial_regs bi edge) (mkreg [] true None);
     mkreg (mk_frame_cells (XA bi edge) (Int64.repr 256)) true (Some 16);
     mkreg (byte_cells 0 32 1) true (Some 32)].
Proof. reflexivity. Qed.

Section FRAME.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block)
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

Lemma scalar_reader_entries id ent :
  flookup scalar_reader_table id = Some ent ->
  (exists b, Genv.find_symbol secp_ge id = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True | FOra fd oracle => oracle_ok secp_ge rd_ev rd_inv rd_ext fd oracle end.
Proof.
  cbn [scalar_reader_table flookup].
  destruct (Pos.eqb C.jets._read8s id) eqn:HId.
  - apply Pos.eqb_eq in HId; subst id; intros HEnt; inversion HEnt; subst ent.
    split.
    + destruct (secp_core_helpers_entries C.jets._read8s C.jets.f_read8s)
        as [b1 [b2 [H1 [H2 [H3 H4]]]]].
      { unfold secp_core_helpers; do 19 right; left; reflexivity. }
      exists b2; split; assumption.
    + apply orc_rd8_ok; try assumption; rewrite HLength; reflexivity.
  - cbn [secp_shift64_table flookup].
    destruct (Pos.eqb jets_secp._secp256k1_u128_rshift id) eqn:HShift.
    + apply Pos.eqb_eq in HShift; subst id; intros HEnt; inversion HEnt; subst ent.
      split.
      * apply secp_pure_ok; unfold secp_pure; do 6 right; left; reflexivity.
      * apply shift64_frame_oracle; exact HOutput.
    + intro HEnt; destruct (int_table_lookup _ _ _ HEnt) as [fd [HEntry HIn]].
      rewrite HEntry; split; [apply secp_pure_ok; exact HIn|exact I].
Qed.

Lemma scalar_reader_events :
  solves rd_ev (read_fe_rho ibits rc) (slog (scalar_reader_state bi (Ptrofs.repr edge))).
Proof.
  rewrite scalar_reader_log_eq; unfold scalar_reader_log.
  rewrite <- (read_fe_selected_log bi (Ptrofs.repr edge) (read_fe_rho ibits rc) β0).
  apply read_fe_input_events with (layout := [(1%positive, 0)]).
Qed.

Local Opaque secp_ge xfun scalar_reader_tree scalar_reader_state.
Theorem exec_scalar_reader_first m layout e le :
  rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m ->
  tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le ->
  ematch layout scalar_reader_venv e ->
  xsep rd_ext layout -> rd_inv (read_fe_rho ibits rc) [] m ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m scalar_reader_first E0 le' mf Out_normal /\
    rep (read_fe_rho ibits rc) layout (sregs (scalar_reader_state bi (Ptrofs.repr edge))) mf /\
    tmatch (read_fe_rho ibits rc) layout scalar_reader_temps le' /\
    rd_inv (read_fe_rho ibits rc) (scalar_reader_log bi (Ptrofs.repr edge)) mf /\
    lframe (frame rd_ext layout (sregs (scalar_reader_initial bi (Ptrofs.repr edge))) m) m mf.
Proof.
  intros HRep HTemps HEnv HSep HInv.
  destruct (xstmt_sound secp_ge [] scalar_reader_table rd_ev rd_inv rd_ext)
    with (n := 1000%nat) (ve := scalar_reader_venv)
      (Σ := scalar_reader_initial bi (Ptrofs.repr edge)) (s := scalar_reader_first)
      (r := RDone (scalar_reader_state bi (Ptrofs.repr edge)) ONormal)
      (ρ := read_fe_rho ibits rc) (β := layout) (m := m) (e := e) (le := le)
    as [le' [mf [out [HExec HPost]]]].
  - apply invA_stable; exact HOutput.
  - apply invA_valid.
  - apply scalar_reader_entries.
  - apply scalar_reader_run_eq.
  - exact HRep.
  - exact HTemps.
  - exact HEnv.
  - split; intros id r ty HImpossible; discriminate.
  - exact HSep.
  - exact HInv.
  - cbn [rsel fst]; apply scalar_reader_events.
  - cbn [post rsel fst snd] in HPost.
    destruct HPost as [HFinal [HTemp [HOut [HShape [HFinalInv HFrame]]]]].
    destruct out; cbn [outmatch] in HOut; try contradiction.
    change (rep (read_fe_rho ibits rc) layout
      (sregs (scalar_reader_state bi (Ptrofs.repr edge))) mf) in HFinal.
    change (tmatch (read_fe_rho ibits rc) layout
      (stemps (scalar_reader_state bi (Ptrofs.repr edge))) le') in HTemp.
    change (rd_inv (read_fe_rho ibits rc)
      (slog (scalar_reader_state bi (Ptrofs.repr edge))) mf) in HFinalInv.
    rewrite scalar_reader_return in HTemp; rewrite scalar_reader_log_eq in HFinalInv.
    exists le', mf; split; [exact HExec|]; split; [exact HFinal|].
    split; [exact HTemp|]; split; assumption.
Qed.
End FRAME.
