(** Actual inverse entry and pure initialization/copies at the linked GE.
    The divstep loop is separate; no source counter execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_clight_internal_frame C.jet_secp_point_mul_storage C.jet_secp_b32_exec C.jet_secp_local_regions
 C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies
 C.jet_secp_fe_inv_prefix C.jet_secp_modinfo_fe_global C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_internal C.jet_clight_internal_preserve C.jet_clight_internal_permissions
 C.jet_transport C.jet_transport_locals.
Require Import C.jet_transport_entry.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_inverse_vars_checked:
 vars_okb secp_ge elements_taptweak_ge(fn_vars f_secp256k1_modinv64_var)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_inverse_ready_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_modinv64_var))inv_ready_prefix=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_inverse_ready_closed:
 closed_stmtb elements_taptweak_curve_helpers inv_ready_prefix=Datatypes.true /\
 forallb(fun local=>nonfunction_type(snd local))(fn_vars f_secp256k1_modinv64_var)=Datatypes.true.
Proof. vm_compute;split;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block elements_taptweak_curve_helpers.
Lemma elements_taptweak_inv_start_rep_from_storage w m bs:
 bs<>elements_taptweak_modinfo_fe_block ->fe_at m bs 0(words5 w) ->Mem.range_perm m bs 0 40 Cur Freeable ->
 elements_taptweak_modinfo_fe_global_rep m ->rep w [(bs,0);(elements_taptweak_modinfo_fe_block,0)]inv_start_regs m.
Proof.
 intros Sep Field Free(Valid & Read & Loads).
 apply two_region_rep_separate;[reflexivity|exact Sep| |].
 - apply owned_field_slice_region;[reflexivity|lia|lia|exact Field|exact Free].
 - apply region_u64;cbn[bas blk lay nth fst snd].
   + lia.
   + exists 0;reflexivity.
   + change(48<=18446744073709551615);lia.
   + exact Valid.
   + exact Read.
   + intros i x At;rewrite nth_error_map in At.
     destruct(nth_error modinfo_fe_words i)as[v|]eqn:Word;[|discriminate].
     injection At as <-;split;[exact(Loads i v Word)|reflexivity].
Qed.
Theorem elements_taptweak_inv_entry_to_loop rho beta m:
 rep rho beta inv_start_regs m ->bas beta 1=0 ->exists betaN e le mi lef mf,
 function_entry2 elements_taptweak_ge f_secp256k1_modinv64_var(map(den rho(lay beta))inv_start_args)m e le mi /\
 Clight2.exec_stmt elements_taptweak_ge e le mi inv_ready_prefix E0 lef mf Out_normal /\
 rep rho(beta++betaN)inv_fg_regs mf /\tmatch rho(beta++betaN)inv_loop_start_temps lef /\
 ematch(beta++betaN)(snd inv_start_alloc)e /\lef!_len=Some(Vint(Int.repr 5)) /\lef!_eta=Some(Vlong(Int64.repr(-1))) /\
 Forall(fun p=>~Mem.valid_block m(fst p))betaN /\
 lframe(fun b ofs=>~foot(beta++betaN)(map rshape(sregs inv_start_state))b ofs)m mf /\
 readonly_preserved m mf /\keeps_permissions m mf.
Proof.
 intros Start Base.
 destruct(inv_entry_to_loop rho beta m Start Base)
 as(betaN & e & le & mi & lef & mf & Entry & Prefix & Objects & Temps & Env & Len & Eta & Fresh & Frame).
 assert(EntryT:function_entry2 elements_taptweak_ge f_secp256k1_modinv64_var
 (map(den rho(lay beta))inv_start_args)m e le mi).
 { eapply function_entry2_transport;[exact elements_taptweak_inverse_vars_checked|exact Entry]. }
 assert(PrefixT:Clight2.exec_stmt elements_taptweak_ge e le mi inv_ready_prefix E0 lef mf Out_normal).
 { eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
    (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
    elements_taptweak_curve_entries elements_taptweak_curve_ok)));
   [exact Prefix|eapply function_entry2_domain;exact Entry|eapply function_entry2_bound;exact Entry|exact elements_taptweak_inverse_ready_checked]. }
 destruct elements_taptweak_inverse_ready_closed as[Closed Vars].
 assert(Plain:plain_env e)by(eapply entry_plain;[exact EntryT|exact Vars]).
 assert(Read:readonly_preserved m mf).
 { eapply preserved_trans;[eapply entry_preserved;exact EntryT|].
   eapply(proj1(internal_exec_preserved _ _ elements_taptweak_internal_table));[exact PrefixT|exact Plain|exact Closed]. }
 assert(Keep:keeps_permissions m mf).
 { eapply keeps_permissions_trans;[eapply entry_keeps_permissions;exact EntryT|].
   eapply(proj1(internal_exec_keeps_permissions _ _ elements_taptweak_internal_table));[exact PrefixT|exact Plain|exact Closed]. }
 exists betaN,e,le,mi,lef,mf;split;[exact EntryT|];split;[exact PrefixT|];split;[exact Objects|];split;[exact Temps|];
 split;[exact Env|];split;[exact Len|];split;[exact Eta|];split;[exact Fresh|];split;[exact Frame|];split;[exact Read|exact Keep].
Qed.
