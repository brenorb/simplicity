(** The actual four-local ecmult entry, three state stores, callee and free layout. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Globalenvs Maps Memory Values Events.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_secp_ecmult_entry C.jet_secp_ecmult_state
 C.jet_secp_ecmult_generator C.jet_secp_curve_statements C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_parse_start C.jet_transport C.jet_transport_locals.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_ecmult_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_ecmult)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_ecmult_initialize_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult))ecmult_state_initialize=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_strauss_lookup:
 secp_helper_lookup elements_taptweak_ge(_secp256k1_ecmult_strauss_wnaf,f_secp256k1_ecmult_strauss_wnaf)=
 Some(Internal f_secp256k1_ecmult_strauss_wnaf).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_ecmult_local_blocks bx ba bp bs:
 blocks_of_env elements_taptweak_ge(ecmult_env bx ba bp bs)=
 [(bs,0,24);(bx,0,320);(bp,0,1040);(ba,0,704)].
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge secp_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_ecmult_env_domain bx ba bp bs:
 edom(ecmult_env bx ba bp bs)(fn_vars f_secp256k1_ecmult).
Proof.
 intros id b ty At;unfold ecmult_env in At.
 repeat rewrite PTree.gsspec in At.
 repeat match type of At with context[if ?test then _ else _]=>destruct test end;
 try(rewrite PTree.gempty in At;discriminate).
 all:injection At as <- <-;subst;cbn[fn_vars In];repeat first[left;reflexivity|right].
Qed.
Lemma elements_taptweak_ecmult_env_bound bx ba bp bs id:
 In id(map fst(fn_vars f_secp256k1_ecmult)) ->exists b ty,(ecmult_env bx ba bp bs)!id=Some(b,ty).
Proof.
 intro Member;cbn[fn_vars map fst In]in Member.
 repeat destruct Member as[Same|Member];try contradiction;subst id;eexists;eexists;reflexivity.
Qed.
Theorem elements_taptweak_ecmult_entry_and_state m r a na ng :
 exists mi mf bx ba bp bs,
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult [r;a;na;ng] m
  (ecmult_env bx ba bp bs) (ecmult_temps r a na ng) mi /\
 Clight2.exec_stmt elements_taptweak_ge (ecmult_env bx ba bp bs) (ecmult_temps r a na ng)
  mi ecmult_state_initialize E0 (ecmult_temps r a na ng) mf Out_normal /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr ba Ptrofs.zero) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 NoDup [bx;ba;bp;bs] /\
 (forall b,Mem.valid_block m b -> ~ In b [bx;ba;bp;bs]) /\
 (forall b hi,In (b,hi) [(bx,320);(ba,704);(bp,1040);(bs,24)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 Mem.unchanged_on (fun _ _=>True) m mf.
Proof.
 destruct(ecmult_entry_and_state m r a na ng)as(mi & mf & bx & ba & bp & bs & Entry & Init & Rest).
 exists mi,mf,bx,ba,bp,bs;split.
 - inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
   constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
   eapply(alloc_variables_transport secp_ge elements_taptweak_ge);[exact Alloc|exact elements_taptweak_ecmult_vars_checked].
 - split;[|exact Rest].
   eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
    (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
    elements_taptweak_curve_entries elements_taptweak_curve_ok)));
   [exact Init|apply elements_taptweak_ecmult_env_domain|apply elements_taptweak_ecmult_env_bound|exact elements_taptweak_ecmult_initialize_checked].
Qed.
Lemma exec_elements_taptweak_strauss_call result args vargs v e le m mf:
 e!_secp256k1_ecmult_strauss_wnaf=None ->
 eval_exprlist elements_taptweak_ge e le m args(type_of_params(fn_params f_secp256k1_ecmult_strauss_wnaf))vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal f_secp256k1_ecmult_strauss_wnaf)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m
 (curve_call _secp256k1_ecmult_strauss_wnaf f_secp256k1_ecmult_strauss_wnaf result args)E0(set_opttemp result v le)mf Out_normal.
Proof.
 intros Global Args Call.
 destruct(secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_strauss_lookup)as(bf & Symbol & Funct).
 eapply exec_elements_taptweak_curve_call with(bf:=bf);[exact Symbol| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
Qed.
