(** Reuse the existing internal-call permission theorem for arbitrary field
    slices. A writable slice need not carry a fictitious allocation at zero;
    real caller ownership survives every checked closed internal execution. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_linkage C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_permissions.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem secp_internal_keeps_permissions fd m args t mf result :
 closed_stmtb secp_closed_helpers (fn_body fd)=true ->
 forallb (fun local=>nonfunction_type (snd local)) (fn_vars fd)=true ->
 Clight2.eval_funcall secp_ge m (Internal fd) args t mf result -> keeps_permissions m mf.
Proof.
 intros Closed Vars Run;inversion Run;subst.
 match goal with
 | Entry:function_entry2 secp_ge _ _ ?ma ?e _ ?mi,
   Free:Mem.free_list ?mo (blocks_of_env secp_ge ?e)=Some ?mz |- _ =>
   pose proof (entry_keeps_permissions _ _ _ _ _ _ _ Entry) as EntryP;
   assert (BodyP:keeps_permissions mi mo) by
    (eapply (proj1 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok));
      [eassumption|eapply entry_plain;[exact Entry|exact Vars]|exact Closed]);
   intros b ofs k p Perm;eapply free_list_avoids;
    [exact Free| |apply BodyP,EntryP;exact Perm];
   eapply entry_blocks_avoid;[exact Entry|eapply Mem.perm_valid_block;exact Perm]
 end.
Qed.

Lemma keeps_range_permissions m mf b lo hi k p : keeps_permissions m mf ->
 Mem.range_perm m b lo hi k p -> Mem.range_perm mf b lo hi k p.
Proof. intros Keep Range pos Pos;apply Keep,Range;exact Pos. Qed.
