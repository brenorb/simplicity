(** Transport the actual Strauss locals and its pure statement phases.
    The scalar split, beta globals, generator tables and external calls are
    handled by their own linked execution proofs. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_secp_generator_entry
 C.jet_secp_generator_globalz_call C.jet_secp_generator_loop_control
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport
 C.jet_transport C.jet_transport_locals C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_strauss_statements:=
 [generator_double_statement;generator_nongenerator_statement;generator_globalz_statement].
Lemma elements_taptweak_strauss_statements_checked:
 forallb(locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)))elements_taptweak_strauss_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_strauss_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_ecmult_strauss_wnaf)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_strauss_env_domain bt bz b0 b128 bw0 bw128 bj bn bl:
 edom(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)(fn_vars f_secp256k1_ecmult_strauss_wnaf).
Proof.
 intros id b ty At;unfold generator_local_env in At.
 repeat rewrite PTree.gsspec in At.
 repeat match type of At with context[if ?test then _ else _]=>destruct test end;
 try(rewrite PTree.gempty in At;discriminate).
 all:injection At as <- <-;subst;cbn[fn_vars In];repeat first[left;reflexivity|right].
Qed.
Lemma elements_taptweak_strauss_env_bound bt bz b0 b128 bw0 bw128 bj bn bl id:
 In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->
 exists b ty,(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)!id=Some(b,ty).
Proof.
 intro Member;cbn[fn_vars map fst In]in Member.
 repeat destruct Member as[Same|Member];try contradiction;subst id;eexists;eexists;reflexivity.
Qed.
Theorem elements_taptweak_strauss_bound_statement_transport e le m stmt trace lef mf out:
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 In stmt elements_taptweak_strauss_statements ->
 Clight2.exec_stmt secp_ge e le m stmt trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge e le m stmt trace lef mf out.
Proof.
 intros Domain Bound Member Run.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok))).
 - exact Run.
 - exact Domain.
 - exact Bound.
 - pose proof elements_taptweak_strauss_statements_checked as Checked.
   rewrite forallb_forall in Checked;exact(Checked stmt Member).
Qed.
Theorem elements_taptweak_strauss_statement_transport bt bz b0 b128 bw0 bw128 bj bn bl
 le m stmt trace lef mf out:
 In stmt elements_taptweak_strauss_statements ->
 Clight2.exec_stmt secp_ge(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)le m stmt trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)le m stmt trace lef mf out.
Proof.
 intros Member Run.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok))).
 - exact Run.
 - apply elements_taptweak_strauss_env_domain.
 - apply elements_taptweak_strauss_env_bound.
 - pose proof elements_taptweak_strauss_statements_checked as Checked.
   rewrite forallb_forall in Checked;exact(Checked stmt Member).
Qed.
Theorem elements_taptweak_strauss_entry_owned m bs r a na ng:
 exists mi bt bz b0 b128 bw0 bw128 bj bn bl,
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult_strauss_wnaf
 [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;na;ng]
 m(generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)(strauss_entry_temps bs r a na ng)mi /\
 NoDup[bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b ->~In b[bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In(b,hi)(generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
 Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe(fun _ _=>True)m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct(strauss_entry_owned m bs r a na ng)as(mi & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl & Entry & Memory).
 exists mi,bt,bz,b0,b128,bw0,bw128,bj,bn,bl;split;[|exact Memory].
 inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply(alloc_variables_transport secp_ge elements_taptweak_ge);[exact Alloc|exact elements_taptweak_strauss_vars_checked].
Qed.
