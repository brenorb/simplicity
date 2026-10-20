(** First original-C field-multiplication checkpoint, through d >>= 52. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_checkpoint_ops.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition mul_spine := fst (split_statement_last (fn_body f_secp256k1_fe_mul_inner)).
Definition mul_last := snd (split_statement_last (fn_body f_secp256k1_fe_mul_inner)).
Definition prefix_spine := firstn 32 mul_spine.
Definition prefix_statement := statement_sequence prefix_spine Sskip.
Definition suffix_statement := statement_sequence (skipn 32 mul_spine) mul_last.
Lemma prefix_suffix_source : statement_sequence prefix_spine suffix_statement = fn_body f_secp256k1_fe_mul_inner.
Proof. Timeout 10 reflexivity. Qed.

Definition mul_allocated := match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
    (fn_vars f_secp256k1_fe_mul_inner) 2 with Some p => p | None => ([], []) end.
Definition prefix_temps := PTree.set _b (XP 1 0)
  (PTree.set _a (XP 0 0) (PTree.set _r (XP 0 0) (PTree.empty sx))).
Definition prefix_initial := mkst prefix_temps (field_mul_regs ++ fst mul_allocated) [] 10.
Definition prefix_run := xstmt (genv_cenv secp_ge) [] field_table 200
  (snd mul_allocated) prefix_initial prefix_statement.
Lemma prefix_completes : match prefix_run with Some (RDone _ ONormal) => true | _ => false end = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Definition prefix_state := match prefix_run with Some (RDone st _) => st | _ => prefix_initial end.
Lemma prefix_run_eq : prefix_run = Some (RDone prefix_state ONormal).
Proof.
  pose proof prefix_completes as H; unfold prefix_state.
  destruct prefix_run as [r|]; [|discriminate].
  destruct r; [destruct o; try discriminate; reflexivity|discriminate].
Qed.

Definition first_c := sx_product (XLv 4) (XLv 9).
Definition first_d :=
  sx_accum (sx_accum (sx_accum (sx_product (XLv 0) (XLv 8)) (XLv 1) (XLv 7))
    (XLv 2) (XLv 6)) (XLv 3) (XLv 5).
Definition first_fold_d := sx_accum first_d (XLc (Int64.repr 68719492368)) (fst first_c).
Definition first_t3 := XLb Band (fst first_fold_d) (XLc (Int64.repr 4503599627370495)).
Definition first_final_c := sx_shift64 first_c.
Definition first_final_d := sx_shift52 first_fold_d.
Lemma prefix_c_low : xload (sregs prefix_state) 2 0 tulong = Some (fst first_final_c).
Proof. Timeout 10 reflexivity. Qed.
Lemma prefix_c_high : xload (sregs prefix_state) 2 8 tulong = Some (snd first_final_c).
Proof. Timeout 10 reflexivity. Qed.
Lemma prefix_d_low : xload (sregs prefix_state) 3 0 tulong = Some (fst first_final_d).
Proof. Timeout 10 reflexivity. Qed.
Lemma prefix_d_high : xload (sregs prefix_state) 3 8 tulong = Some (snd first_final_d).
Proof. Timeout 10 reflexivity. Qed.
Lemma prefix_t3 : (stemps prefix_state)!_t3 = Some first_t3.
Proof. Timeout 10 reflexivity. Qed.

Theorem field_stmt_normal fuel ve st stmt st' :
  xstmt (genv_cenv secp_ge) [] field_table fuel ve st stmt = Some (RDone st' ONormal) ->
  forall rho beta e le m,
    rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le -> ematch beta ve e ->
    exists le' mf,
      Clight2.exec_stmt secp_ge e le m stmt E0 le' mf Out_normal /\
      rep rho beta (sregs st') mf /\ tmatch rho beta (stemps st') le' /\
      map rshape (sregs st') = map rshape (sregs st) /\
      lframe (fun b ofs => ~ foot beta (map rshape (sregs st)) b ofs) m mf.
Proof.
  intros H rho beta e le m HR HT HE.
  destruct (xstmt_sound secp_ge [] field_table (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
    ltac:(auto) ltac:(intros; contradiction) field_table_correct
    fuel ve st stmt (RDone st' ONormal) H rho beta e le m HR HT HE)
    as (le' & mf & out & HX & HP).
  - split; intros; discriminate.
  - intros r _ [].
  - exact I.
  - apply Forall_forall; intros; exact I.
  - destruct HP as (HRep & HTm & HO & HS & _ & HF).
    cbn [rsel fst snd] in HRep, HTm, HO, HS.
    destruct out; cbn [outmatch] in HO; try contradiction.
    exists le', mf; split; [exact HX|]; split; [exact HRep|]; split; [exact HTm|];
      split; [exact HS|].
    eapply lframe_implies; [exact HF|].
    intros b ofs HOutside HValid; split; [exact HValid|]; split; [exact HOutside|tauto].
Qed.

Local Opaque xstmt prefix_state prefix_statement mul_allocated prefix_initial prefix_temps.
Lemma prefix_typed_run : xstmt (genv_cenv secp_ge) [] field_table 200 (snd mul_allocated)
  prefix_initial prefix_statement = Some (RDone prefix_state ONormal).
Proof. change (prefix_run = Some (RDone prefix_state ONormal)); exact prefix_run_eq. Qed.
Theorem exec_field_first_checkpoint rho beta e le m :
  rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m prefix_statement E0 le' mf Out_normal /\
    rep rho beta (sregs prefix_state) mf /\ tmatch rho beta (stemps prefix_state) le' /\
    map rshape (sregs prefix_state) = map rshape (sregs prefix_initial) /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  exact (field_stmt_normal 200 (snd mul_allocated) prefix_initial prefix_statement prefix_state
    prefix_typed_run rho beta e le m).
Qed.
