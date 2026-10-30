(** Actual linked Strauss entry and initialization, reusing the original
    allocation/ownership witnesses and transporting only the pure initializer. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_secp_generator_entry
 C.jet_secp_generator_initialize C.jet_secp_point_set_bit C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_strauss_transport
 C.jet_transport C.jet_transport_locals C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_strauss_initialize_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf))generator_initialize=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Theorem elements_taptweak_strauss_entry_and_initialize m bs r a na ng :
 exists mi mf bt bz b0 b128 bw0 bw128 bj bn bl,
 function_entry2 elements_taptweak_ge f_secp256k1_ecmult_strauss_wnaf
  [Vptr bs Ptrofs.zero;r;Vlong Int64.one;a;na;ng]
  m (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) (strauss_entry_temps bs r a na ng) mi /\
 Clight2.exec_stmt elements_taptweak_ge (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)
  (strauss_entry_temps bs r a na ng) mi generator_initialize E0
  (generator_initial_temps (strauss_entry_temps bs r a na ng)) mf Out_normal /\
 fe_at mf bz 0 (words5 (point_set_bit_words true)) /\
 NoDup [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\
 (forall b,Mem.valid_block m b -> ~ In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) /\
 (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mf /\ keeps_permissions m mf /\ readonly_preserved m mf.
Proof.
 destruct(strauss_entry_and_initialize m bs r a na ng)
 as(mi & mf & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl & Entry & Init & Rest).
 exists mi,mf,bt,bz,b0,b128,bw0,bw128,bj,bn,bl;split.
 - inversion Entry as[Vars Params Disjoint Alloc Bind];subst.
   constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
   eapply(alloc_variables_transport secp_ge elements_taptweak_ge);[exact Alloc|exact elements_taptweak_strauss_vars_checked].
 - split;[|exact Rest].
   eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
    (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
    elements_taptweak_curve_entries elements_taptweak_curve_ok)));
   [exact Init|apply elements_taptweak_strauss_env_domain|apply elements_taptweak_strauss_env_bound|exact elements_taptweak_strauss_initialize_checked].
Qed.
