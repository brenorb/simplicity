(** Same-memory transport of the original wNAF pure phases and real entry.
    The external clear is deliberately outside this checked phase list. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_secp_wnaf_digit C.jet_secp_wnaf_control
 C.jet_secp_wnaf_prepare C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_entry5
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport C.jet_transport C.jet_transport_locals.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_wnaf_statements:=[wnaf_before_memset;wnaf_post_memset].
Lemma elements_taptweak_wnaf_statements_checked:
 forallb(locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult_wnaf)))elements_taptweak_wnaf_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_wnaf_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_ecmult_wnaf)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_wnaf_scalar_size:sizeof elements_taptweak_ge(Tstruct __5826 noattr)=32.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_wnaf_env_domain bs:edom(wnaf_env bs)(fn_vars f_secp256k1_ecmult_wnaf).
Proof.
 intros id b ty At;unfold wnaf_env in At;rewrite PTree.gsspec in At.
 destruct(peq id _s)as[Same|Other].
 - subst id;injection At as <- <-;left;reflexivity.
 - rewrite PTree.gempty in At;discriminate.
Qed.
Lemma elements_taptweak_wnaf_env_bound bs id:In id(map fst(fn_vars f_secp256k1_ecmult_wnaf)) ->
 exists b ty,(wnaf_env bs)!id=Some(b,ty).
Proof.
 intro Member;cbn[fn_vars map fst In]in Member;destruct Member as[Same|[]];subst id.
 eexists;eexists;reflexivity.
Qed.
Theorem elements_taptweak_wnaf_statement_transport bs le m stmt trace lef mf out:
 In stmt elements_taptweak_wnaf_statements ->
 Clight2.exec_stmt secp_ge(wnaf_env bs)le m stmt trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge(wnaf_env bs)le m stmt trace lef mf out.
Proof.
 intros Member Run.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok))).
 - exact Run.
 - apply elements_taptweak_wnaf_env_domain.
 - apply elements_taptweak_wnaf_env_bound.
 - pose proof elements_taptweak_wnaf_statements_checked as Checked.
   rewrite forallb_forall in Checked;exact(Checked stmt Member).
Qed.
Lemma elements_taptweak_wnaf_entry_transport args m bs le mi:
 function_entry2 secp_ge f_secp256k1_ecmult_wnaf args m(wnaf_env bs)le mi ->
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult_wnaf args m(wnaf_env bs)le mi.
Proof.
 intro Entry;inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply(alloc_variables_transport secp_ge elements_taptweak_ge);[exact Alloc|exact elements_taptweak_wnaf_vars_checked].
Qed.
Lemma elements_taptweak_wnaf_entry5 m mi bs b base a:Mem.alloc m 0 32=(mi,bs) ->
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult_wnaf
 [Vptr b(Ptrofs.repr base);Vint(Int.repr 129);a;Vint(Int.repr 5)]m(wnaf_env bs)(wnaf_entry5_temps b base a)mi.
Proof. intro Alloc;apply elements_taptweak_wnaf_entry_transport;apply wnaf_entry5;exact Alloc. Qed.
Lemma elements_taptweak_wnaf_entry15 m mi bs b base a:Mem.alloc m 0 32=(mi,bs) ->
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult_wnaf
 [Vptr b(Ptrofs.repr base);Vint(Int.repr 129);a;Vint(Int.repr 15)]m(wnaf_env bs)(wnaf_entry15_temps b base a)mi.
Proof. intro Alloc;apply elements_taptweak_wnaf_entry_transport;apply wnaf_entry15;exact Alloc. Qed.
Lemma elements_taptweak_wnaf_local_blocks bs:blocks_of_env elements_taptweak_ge(wnaf_env bs)=[(bs,0,32)].
Proof.
 change([(bs,0,sizeof elements_taptweak_ge(Tstruct __5826 noattr))]=[(bs,0,32)]).
 rewrite elements_taptweak_wnaf_scalar_size;reflexivity.
Qed.
Lemma exec_elements_taptweak_wnaf_before5 bs le m:
 le!_len=Some(Vint(Int.repr 129)) ->le!_w=Some(Vint(Int.repr 5)) ->
 Clight2.exec_stmt elements_taptweak_ge(wnaf_env bs)le m wnaf_before_memset E0(wnaf_before_temps le)m Out_normal.
Proof.
 intros Len W;eapply elements_taptweak_wnaf_statement_transport;
 [left;reflexivity|apply exec_wnaf_before_memset5;assumption].
Qed.
Lemma exec_elements_taptweak_wnaf_before15 bs le m:
 le!_len=Some(Vint(Int.repr 129)) ->le!_w=Some(Vint(Int.repr 15)) ->
 Clight2.exec_stmt elements_taptweak_ge(wnaf_env bs)le m wnaf_before_memset E0(wnaf_before_temps le)m Out_normal.
Proof.
 intros Len W;eapply elements_taptweak_wnaf_statement_transport;
 [left;reflexivity|apply exec_wnaf_before_memset15;assumption].
Qed.
