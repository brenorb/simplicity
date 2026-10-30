(** Reusable entry/domain transport for the original Clight function entry. *)
From Coq Require Import List.
From compcert Require Import AST Ctypes Clight ClightBigstep Maps Memory Values.
Require Import C.jet_transport C.jet_transport_locals.
Set Default Timeout 10.
Lemma function_entry2_domain ge f args m e le mi:
 function_entry2 ge f args m e le mi ->edom e(fn_vars f).
Proof.
 intro Entry;inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
 intros id b ty At;destruct(alloc_variables_dom ge _ _ _ _ _ Alloc id b ty At)as[Empty|Member].
 - rewrite PTree.gempty in Empty;discriminate.
 - exact Member.
Qed.
Lemma function_entry2_bound ge f args m e le mi:
 function_entry2 ge f args m e le mi ->forall id,In id(map fst(fn_vars f)) ->exists b ty,e!id=Some(b,ty).
Proof.
 intros Entry id Member;inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
 eapply locals_alloc_variables_bound;[exact Alloc|right;exact Member].
Qed.
Theorem function_entry2_transport ge1 ge2 f args m e le mi:
 vars_okb ge1 ge2(fn_vars f)=true ->function_entry2 ge1 f args m e le mi ->
 function_entry2 ge2 f args m e le mi.
Proof.
 intros Checked Entry;inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply(alloc_variables_transport ge1 ge2);[exact Alloc|exact Checked].
Qed.
