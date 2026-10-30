(** Pure inverse phases under the real five-local environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_sx_state C.jet_sx_eval C.jet_secp_linkage C.jet_secp_statement_prefix
 C.jet_secp_modinv_var_de C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies C.jet_secp_modinv_var_first_batch
 C.jet_secp_modinv_var_batch_update C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_finish
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_internal C.jet_transport C.jet_transport_locals C.jet_clight_internal_frame.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_inverse_pure_phases :=
 [inv_divstep_loads;inv_return_eta;inv_after_divsteps;inv_finish].
Lemma elements_taptweak_inverse_phases_checked:
 forallb(locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_modinv64_var)))elements_taptweak_inverse_pure_phases=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_inverse_phases_closed:
 forallb(closed_stmtb elements_taptweak_curve_helpers)elements_taptweak_inverse_pure_phases=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_inverse_divstep_arguments_checked:
 locals_exprs_okb secp_ge elements_taptweak_ge(map fst(fn_vars f_secp256k1_modinv64_var))
 [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_divsteps_helper_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_modinv64_divsteps_62_var=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_modinv64_divsteps_62_var).
Proof. exists(elements_taptweak_symbol_block _secp256k1_modinv64_divsteps_62_var);split;vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_inverse_env_domain beta e:
 ematch beta(snd inv_start_alloc)e ->edom e(fn_vars f_secp256k1_modinv64_var).
Proof.
 intros Env id b ty At;rewrite(proj1(Env id))in At;cbn[inv_start_alloc snd vlookup]in At.
 repeat match type of At with context[if ?D then _ else _]=>destruct D eqn:? end;try discriminate.
 all:repeat match goal with H:Pos.eqb _ _=Datatypes.true |- _=>apply Pos.eqb_eq in H end;
 subst;injection At as <- <-;cbn[f_secp256k1_modinv64_var fn_vars In];tauto.
Qed.
Lemma elements_taptweak_inverse_env_bound beta e:
 ematch beta(snd inv_start_alloc)e ->forall id,In id(map fst(fn_vars f_secp256k1_modinv64_var)) ->
 exists b ty,e!id=Some(b,ty).
Proof.
 intros Env id Member;cbn[f_secp256k1_modinv64_var fn_vars map fst In]in Member.
 repeat destruct Member as[Same|Member];try contradiction;subst id;
 rewrite(proj1(Env _));eexists;eexists;reflexivity.
Qed.
Theorem elements_taptweak_inverse_pure_exec beta e le m s trace lef mf out:
 ematch beta(snd inv_start_alloc)e ->In s elements_taptweak_inverse_pure_phases ->
 Clight2.exec_stmt secp_ge e le m s trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge e le m s trace lef mf out.
Proof.
 intros Env Member Run;pose proof elements_taptweak_inverse_phases_checked as Checked.
 rewrite forallb_forall in Checked.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok)));
 [exact Run|eapply elements_taptweak_inverse_env_domain;exact Env|
 eapply elements_taptweak_inverse_env_bound;exact Env|exact(Checked s Member)].
Qed.
