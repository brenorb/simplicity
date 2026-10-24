(** A checked closed subset of the original internal helper table. Reuse the
    existing Clight readonly-preservation proof; no external-call properties
    or determinism are used. In particular the CTZ path is NOT in this set. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_clight_readonly C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies
 C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_finish C.jet_sx_eval.
Import ListNotations.
Set Default Timeout 10.
Local Opaque secp_ge.

Fixpoint secp_closed_prune fuel (table:list(ident*function)) :=
 match fuel with O=>table | S k=>secp_closed_prune k
  (filter(fun it=>closed_stmtb table (fn_body(snd it))) table) end.
Definition secp_closed_ids := Eval vm_compute in map fst (secp_closed_prune 10 secp_pure).
Definition secp_closed_helpers := filter
 (fun it=>existsb (Pos.eqb(fst it)) secp_closed_ids) secp_pure.
Lemma secp_closed_helpers_subset item : In item secp_closed_helpers -> In item secp_pure.
Proof.
 unfold secp_closed_helpers;intro Member;apply filter_In in Member;tauto.
Qed.
Lemma secp_closed_helpers_checked : forallb (fun it=>
 closed_stmtb secp_closed_helpers (fn_body(snd it)) &&
 forallb(fun local=>nonfunction_type(snd local)) (fn_vars(snd it))) secp_closed_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_helpers_count : length secp_closed_helpers=94%nat.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_helpers_ok : internal_table_ok secp_ge secp_closed_helpers.
Proof.
 intros id fd Lookup;pose proof(internal_lookup_in _ _ _ Lookup) as Member.
 pose proof secp_closed_helpers_checked as Checked;rewrite forallb_forall in Checked.
 specialize(Checked (id,fd) Member);apply andb_true_iff in Checked;destruct Checked as[Body Vars].
 split.
 - exact(secp_pure_ok id fd (secp_closed_helpers_subset (id,fd) Member)).
 - split;assumption.
Qed.

Lemma secp_closed_ready_prefix : closed_stmtb secp_closed_helpers inv_ready_prefix=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_after_divsteps : closed_stmtb secp_closed_helpers inv_after_divsteps=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_finish : closed_stmtb secp_closed_helpers inv_finish=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_scalar_pack : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_to_signed62)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_closed_scalar_unpack : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_from_signed62)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_closed_helpers.

Lemma inv_env_plain beta e : ematch beta (snd inv_start_alloc) e -> plain_env e.
Proof.
 intros Env id b ty Local;rewrite(proj1(Env id)) in Local.
 cbn [inv_start_alloc snd vlookup] in Local.
 repeat match type of Local with context[if ?D then _ else _]=>destruct D end;
 try discriminate;injection Local as <- <-;reflexivity.
Qed.
Theorem secp_closed_stmt_preserved e le m stmt t lef mf out :
 Clight2.exec_stmt secp_ge e le m stmt t lef mf out -> plain_env e ->
 closed_stmtb secp_closed_helpers stmt=true -> readonly_preserved m mf.
Proof.
 intros Run Plain Closed;exact(proj1(internal_exec_preserved _ _ secp_closed_helpers_ok)
  e le m stmt t lef mf out Run Plain Closed).
Qed.
Theorem secp_closed_function_preserved fd m args t mf result :
 closed_stmtb secp_closed_helpers (fn_body fd)=true ->
 forallb(fun local=>nonfunction_type(snd local)) (fn_vars fd)=true ->
 Clight2.eval_funcall secp_ge m (Internal fd) args t mf result -> readonly_preserved m mf.
Proof.
 intros Closed Vars Run;inversion Run;subst.
 eapply preserved_trans;[eapply entry_preserved;eassumption|].
 eapply preserved_trans;[|eapply freelist_preserved;eassumption].
 eapply secp_closed_stmt_preserved;[eassumption|eapply entry_plain;eassumption|exact Closed].
Qed.

Lemma secp_preserved_readback m mf : readonly_preserved m mf -> readonly_readback m mf.
Proof.
 intros(Forward & Unchanged);apply readonly_readback_unchanged;[exact Forward|].
 eapply Mem.unchanged_on_implies;[exact Unchanged|].
 intros b ofs NotWritable Valid;split;assumption.
Qed.
