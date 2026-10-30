(** Actual linked inverse loads and divstep call, for either modulus. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.extraMath C.divstep C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_eval
 C.jet_sx_mem C.jet_sx_region_lframe C.jet_sx_u64_transport C.jet_sx_forget_cells
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_entry_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_de
 C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_first_batch
 C.jet_secp_modinv_var_batch_entry C.jet_secp_modinv_var_batch_exit
 C.jet_secp_div62_loop C.jet_secp_div62_exit C.jet_secp_local_regions C.jet_secp_fe_nv
 C.jet_secp_u128_shift64_rep C.jet_secp_statement_prefix.
Require Import C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_elements_taptweak_div62 C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_parse_start C.jet_transport_locals C.jet_secp_modinv_batch_modulus C.jet_ctz_model.
Require Import C.jet_elements_taptweak_inverse_phases.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.

Theorem exec_elements_taptweak_inv_mod_batch(Model:ctz_model)mu len rho st beta e le m :
 -683<=eta st<683 -> (0<len<=5)%nat -> rep rho beta (inv_mod_seed_regs mu) m ->
 ematch beta (snd inv_start_alloc) e -> le!_eta=Some(Vlong(Int64.repr(eta st))) ->
 inv_state_matches len rho st -> exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m inv_divstep_batch E0 (inv_divstep_returned st rho le) mf Out_normal /\
 rep (inv_batch_result_rho st rho) beta (inv_mod_loop_regs mu) mf /\
 inv_matrix_matches (inv_batch_result_rho st rho) st /\
 lframe(fun b _=>b<>blk beta 6) m mf /\ readonly_preserved m mf.
Proof.
 intros EtaRange Length Rep Env Eta State.
 pose proof(exec_inv_divstep_load_values e le m (blk beta 4) (blk beta 5) (rho 15%nat) (rho 20%nat)
  (proj1(Env _f)) (proj1(Env _g)) (inv_mod_batch_low_load mu rho beta m false Rep)
  (inv_mod_batch_low_load mu rho beta m true Rep)) as Loads.
 destruct(rep_free_region rho beta (inv_mod_seed_regs mu) m 6 32 Rep
  ltac:(change(6<7)%nat;lia) eq_refl) as(Base & Free).
 destruct(eval_elements_taptweak_div62 Model m st 62 (rho 15%nat) (rho 20%nat) (blk beta 6)
  ltac:(lia) EtaRange
  ltac:(rewrite(proj1 State);exact(inv_batch_low_modulo len rho false))
  ltac:(rewrite(proj2 State);exact(inv_batch_low_modulo len rho true)) Free)
  as(mf & Call & SignedLoads & ExactLoads & Returned & Owned & Frame & Readonly).
 assert(LoadsT:Clight2.exec_stmt elements_taptweak_ge e le m inv_divstep_loads E0
  (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le)m Out_normal).
 { eapply elements_taptweak_inverse_pure_exec;[exact Env|cbn[elements_taptweak_inverse_pure_phases In];tauto|exact Loads]. }
 assert(Args:eval_exprlist elements_taptweak_ge e(inv_divstep_loaded_values(rho 15%nat)(rho 20%nat)le)m
  [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]
  (type_of_params(fn_params f_secp256k1_modinv64_divsteps_62_var))
  [Vlong(Int64.repr(eta st));Vlong(rho 15%nat);Vlong(rho 20%nat);Vptr(blk beta 6)Ptrofs.zero]).
 { eapply(locals_eval_exprlist_transport secp_ge elements_taptweak_ge)with
    (V:=map fst(fn_vars f_secp256k1_modinv64_var)).
   - eapply elements_taptweak_inverse_env_bound;exact Env.
   - exact(inv_divstep_arguments_values beta e le m (Int64.repr(eta st)) (rho 15%nat) (rho 20%nat) Env Eta).
   - exact elements_taptweak_inverse_divstep_arguments_checked. }
 destruct elements_taptweak_divsteps_helper_linked as(bf & Symbol & Funct).
 assert(ExecCall:Clight2.exec_stmt elements_taptweak_ge e (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le)
  m inv_divstep_call E0 (inv_divstep_returned st rho le) mf Out_normal).
 { unfold inv_divstep_call,inv_divstep_returned;eapply exec_elements_taptweak_curve_call with(bf:=bf)
   (result:=Some _t'1) (v:=Vlong(Int64.repr(eta(fst(stepN 62 st)))))
   (vargs:=[Vlong(Int64.repr(eta st));Vlong(rho 15%nat);Vlong(rho 20%nat);Vptr(blk beta 6) Ptrofs.zero]).
   - exact Symbol.
   - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
   - exact(proj1(Env _secp256k1_modinv64_divsteps_62_var)).
   - exact Args.
   - exact Call. }
 exists mf;split.
 - unfold inv_divstep_batch;eapply exec_statement_prefix_then_last;[exact LoadsT|exact ExecCall].
 - split;[eapply inv_mod_batch_restore;eassumption|];split;[apply inv_batch_result_matrix|];split;assumption.
Qed.
