(** Readonly and permission preservation from the actual linked internal graph.
    No general external-call properties are required. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_internal_checked:
 forallb(fun it=>closed_stmtb elements_taptweak_curve_helpers(fn_body(snd it)) &&
 forallb(fun local=>nonfunction_type(snd local))(fn_vars(snd it)))elements_taptweak_curve_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_internal_body id fd:In(id,fd)elements_taptweak_curve_helpers ->
 closed_stmtb elements_taptweak_curve_helpers(fn_body fd)=true /\
 forallb(fun local=>nonfunction_type(snd local))(fn_vars fd)=true.
Proof.
 intro Member;pose proof elements_taptweak_internal_checked as Checked.
 rewrite forallb_forall in Checked;specialize(Checked(id,fd)Member).
 exact(andb_prop _ _ Checked).
Qed.
Lemma elements_taptweak_internal_table:internal_table_ok elements_taptweak_ge elements_taptweak_curve_helpers.
Proof.
 intros id fd Lookup;pose proof(internal_lookup_in _ _ _ Lookup)as Member.
 destruct(elements_taptweak_curve_entries id fd Member)as(b1 & b2 & S1 & F1 & S2 & F2).
 split;[exists b2;split;assumption|apply(elements_taptweak_internal_body id fd Member)].
Qed.
Theorem elements_taptweak_internal_preserved id fd m args trace mf result:
 In(id,fd)elements_taptweak_curve_helpers ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)args trace mf result ->readonly_preserved m mf.
Proof.
 intros Member Run;destruct(elements_taptweak_internal_body id fd Member)as[Closed Vars].
 inversion Run;subst.
 eapply preserved_trans;[eapply entry_preserved;eassumption|].
 eapply preserved_trans;[|eapply freelist_preserved;eassumption].
 eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));
 [eassumption|eapply entry_plain;eassumption|exact Closed].
Qed.
Theorem elements_taptweak_internal_keeps_permissions id fd m args trace mf result:
 In(id,fd)elements_taptweak_curve_helpers ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)args trace mf result ->keeps_permissions m mf.
Proof.
 intros Member Run;destruct(elements_taptweak_internal_body id fd Member)as[Closed Vars].
 inversion Run;subst.
 match goal with
 | Entry:function_entry2 elements_taptweak_ge _ _ ?ma ?e _ ?mi,
   Free:Mem.free_list ?mo(blocks_of_env elements_taptweak_ge ?e)=Some ?mz |- _=>
   pose proof(entry_keeps_permissions _ _ _ _ _ _ _ Entry)as EntryP;
   assert(BodyP:keeps_permissions mi mo)by
    (eapply(proj1(internal_exec_keeps_permissions _ _ elements_taptweak_internal_table));
     [eassumption|eapply entry_plain;[exact Entry|exact Vars]|exact Closed]);
   intros bb ofs k p Perm;eapply free_list_avoids;
    [exact Free| |apply BodyP,EntryP;exact Perm];
   eapply entry_blocks_avoid;[exact Entry|eapply Mem.perm_valid_block;exact Perm]
 end.
Qed.
