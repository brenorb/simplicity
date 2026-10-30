(** Pure divstep phases and the actual linked counting-call boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight
 ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.extraMath C.divstep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_div62_count C.jet_secp_div62_consume C.jet_secp_div62_entry
 C.jet_secp_div62_finish C.jet_secp_div62_loop C.jet_elements_taptweak_ctz
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_internal
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals C.jet_transport C.jet_transport_locals
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_ctz_model.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_div62_pure_phases :=
 [div62_initializers;div62_after_count;div62_copy_count;div62_finish].
Lemma elements_taptweak_div62_phases_checked:
 forallb(locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)[])
 elements_taptweak_div62_pure_phases=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_div62_finish_closed:
 closed_stmtb elements_taptweak_curve_helpers div62_finish=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_div62_sentinel_checked:
 expr_okb secp_ge elements_taptweak_ge div62_sentinel_expr=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_div62_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_modinv64_divsteps_62_var)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_ctz_helper_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_ctz64_var=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_ctz64_var).
Proof. exists(elements_taptweak_symbol_block _secp256k1_ctz64_var);split;vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_div62_pure_exec le m s trace lef mf out:
 In s elements_taptweak_div62_pure_phases ->
 Clight2.exec_stmt secp_ge empty_env le m s trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge empty_env le m s trace lef mf out.
Proof.
 intros Member Run.
 pose proof elements_taptweak_div62_phases_checked as Checked.
 rewrite forallb_forall in Checked.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok)))with(vars:=[]).
 - exact Run.
 - intros id b ty At;rewrite PTree.gempty in At;discriminate.
 - intros id Impossible;contradiction.
 - exact(Checked s Member).
Qed.
Theorem exec_elements_taptweak_div62_count_call(Model:ctz_model)le m g i:
 0<=i<=62 ->le!_g=Some(Vlong g) ->le!_i=Some(Vint(Int.repr i)) ->
 Clight2.exec_stmt elements_taptweak_ge empty_env le m(Ssequence div62_count_call div62_copy_count)E0
 (div62_counted_temps le(div62_sentinel_count g i))m Out_normal.
Proof.
 intros I G Index;destruct elements_taptweak_ctz_helper_linked as(bf & Symbol & Function).
 eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=m)
 (le1:=PTree.set _t'1(Vint(Int.repr(div62_sentinel_count g i)))le).
 - unfold div62_count_call;eapply exec_Scall with(vf:=Vptr bf Ptrofs.zero)
   (vargs:=[Vlong(div62_sentinel_word g i)])(f:=Internal f_secp256k1_ctz64_var)
   (vres:=Vint(Int.repr(div62_sentinel_count g i))).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs.
     * apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge empty_env le m));
       [eapply eval_div62_sentinel;eassumption|exact elements_taptweak_div62_sentinel_checked].
     * reflexivity.
     * constructor.
   + exact Function.
   + reflexivity.
   + apply eval_elements_taptweak_ctz64;[exact Model|exact(div62_sentinel_nonzero g i I)].
 - apply elements_taptweak_div62_pure_exec;[cbn[elements_taptweak_div62_pure_phases In];tauto|].
   apply exec_div62_copy_count;apply PTree.gss.
Qed.
