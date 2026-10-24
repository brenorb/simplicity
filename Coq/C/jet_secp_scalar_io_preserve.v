(** Original scalar reader/writer calls are closed internal C executions.
    Preserve initialized globals without external-call properties or imposing
    separation between input frame memory and readonly globals. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_secp_closed_helpers C.jet_sx_mem C.jet_sx_pure
 C.jet_secp_modinfo_scalar_global C.jet_secp_modinfo_scalar_initialized
 C.jet_secp_scalar_inverse_caller C.jet_clight_readonly_frame.
Import ListNotations.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Definition scalar_io_base := secp_pure ++ secp_core_helpers ++
 [(_read_scalar,f_read_scalar);(_write_scalar,f_write_scalar)].
Definition scalar_io_ids := Eval vm_compute in map fst (secp_closed_prune 10 scalar_io_base).
Definition scalar_io_helpers := filter
 (fun it=>existsb (Pos.eqb(fst it)) scalar_io_ids) scalar_io_base.
Lemma scalar_io_helpers_checked : forallb (fun it=>
 closed_stmtb scalar_io_helpers (fn_body(snd it)) &&
 forallb(fun local=>nonfunction_type(snd local)) (fn_vars(snd it))) scalar_io_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma scalar_io_helpers_count : length scalar_io_helpers=114%nat.
Proof. vm_compute;reflexivity. Qed.
Lemma scalar_io_base_lookup : map (symbol_lookup secp_ge) scalar_io_base=
 map(fun p=>Some(Internal(snd p))) scalar_io_base.
Proof. vm_compute;reflexivity. Qed.
Lemma scalar_io_helpers_subset item : In item scalar_io_helpers -> In item scalar_io_base.
Proof. unfold scalar_io_helpers;intro Member;apply filter_In in Member;tauto. Qed.
Local Opaque scalar_io_base scalar_io_ids scalar_io_helpers.
Lemma scalar_io_helpers_ok : internal_table_ok secp_ge scalar_io_helpers.
Proof.
 intros id fd Lookup;pose proof(internal_lookup_in _ _ _ Lookup) as Member.
 pose proof scalar_io_helpers_checked as Checked;rewrite forallb_forall in Checked.
 specialize(Checked (id,fd) Member);apply andb_true_iff in Checked;destruct Checked as[Body Vars].
 split;[|split;assumption].
 exact(symbol_lookup_table secp_ge scalar_io_base scalar_io_base_lookup id fd (scalar_io_helpers_subset _ Member)).
Qed.
Lemma scalar_io_allowed : allowed_call scalar_io_helpers (Internal f_read_scalar) /\
 allowed_call scalar_io_helpers (Internal f_write_scalar).
Proof.
 Local Transparent scalar_io_base scalar_io_ids scalar_io_helpers.
 split;[exists _read_scalar,f_read_scalar|exists _write_scalar,f_write_scalar];
 split;[vm_compute;reflexivity|reflexivity|vm_compute;reflexivity|reflexivity].
Qed.
Local Opaque scalar_io_helpers.

Theorem scalar_reader_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal f_read_scalar) args t mf result -> readonly_preserved m mf.
Proof.
 intro Run;exact(proj2(internal_exec_preserved _ _ scalar_io_helpers_ok)
  m _ args t mf result Run (proj1 scalar_io_allowed)).
Qed.
Theorem scalar_writer_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m (Internal f_write_scalar) args t mf result -> readonly_preserved m mf.
Proof.
 intro Run;exact(proj2(internal_exec_preserved _ _ scalar_io_helpers_ok)
  m _ args t mf result Run (proj2 scalar_io_allowed)).
Qed.

Lemma preserved_readonly_block_frame m mf b : readonly_preserved m mf ->
 Mem.valid_block m b -> (forall ofs,~Mem.perm m b ofs Max Writable) ->
 lframe(fun block _=>block=b) m mf.
Proof.
 intros(Forward & Unchanged) Valid NotWritable;split.
 - intros chunk block ofs V Range.
   eapply Mem.load_unchanged_on_1;[exact Unchanged|exact V|].
   intros i I;split;[exact V|rewrite(Range i I);apply NotWritable].
 - split.
   + intros block ofs k p V Same Perm;eapply Mem.perm_unchanged_on;[exact Unchanged| |exact Perm].
     split;[exact V|rewrite Same;apply NotWritable].
   + intros block V;exact(proj1(Forward block V)).
Qed.
Theorem modinfo_scalar_initialized_preserved m mf : modinfo_scalar_initialized m ->
 readonly_preserved m mf -> modinfo_scalar_initialized mf.
Proof.
 intros(Global & Bounds) Preserved.
 pose proof(preserved_readonly_block_frame m mf scalar_inv_modinfo_block Preserved
  (proj1 Global) (readonly_bounds_not_writable _ _ _ _ Bounds)) as Frame.
 assert(GlobalF:modinfo_scalar_global_rep mf).
 { eapply modinfo_scalar_global_lframe;[exact Global|exact Frame|];reflexivity. }
 split;[exact GlobalF|].
 eapply readonly_bounds_transport;[exact(proj1 Global)|exact Bounds|exact(proj1 Preserved)|exact(proj1(proj2 GlobalF))].
Qed.
