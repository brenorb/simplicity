(** Transport the real internal arithmetic dependency slice, permitting
    declared local names that also appear in the global symbol table. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Globalenvs Memory Values Events.
Require Import C.jet_transport C.jet_transport_locals C.jet_elements_taptweak_import
 C.jet_elements_taptweak_pure C.jet_secp_linkage C.jets_secp.
Import ListNotations Ctypes.
Set Default Timeout 10.
Definition elements_taptweak_curve_candidates:=flat_map
 (fun it=>match snd it with Gfun (Internal f)=>[(fst it,f)]|_=>[] end) taptweak_import_definitions.
Fixpoint elements_taptweak_curve_prune fuel (table:list(ident*function)):=
 match fuel with O=>table|S n=>elements_taptweak_curve_prune n
 (filter (fun it=>locals_fundef_okb secp_ge elements_taptweak_ge (map fst table) (Internal (snd it))) table) end.
Definition elements_taptweak_curve_names:=Eval vm_compute in
 map fst (elements_taptweak_curve_prune 10 elements_taptweak_curve_candidates).
Definition elements_taptweak_curve_helpers:=filter
 (fun it=>existsb (Pos.eqb (fst it)) elements_taptweak_curve_names) elements_taptweak_curve_candidates.
Lemma elements_taptweak_curve_closed:
 forallb (fun it=>locals_fundef_okb secp_ge elements_taptweak_ge
 (map fst elements_taptweak_curve_helpers) (Internal (snd it))) elements_taptweak_curve_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_curve_source_lookup:
 map (secp_helper_lookup secp_ge) elements_taptweak_curve_helpers=
 map (fun it=>Some(Internal(snd it))) elements_taptweak_curve_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_curve_target_lookup:
 map (secp_helper_lookup elements_taptweak_ge) elements_taptweak_curve_helpers=
 map (fun it=>Some(Internal(snd it))) elements_taptweak_curve_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_curve_has_decompress:
 In (_secp256k1_ge_set_xo_var,f_secp256k1_ge_set_xo_var) elements_taptweak_curve_helpers.
Proof.
 assert (Found:find (fun it=>Pos.eqb (fst it) _secp256k1_ge_set_xo_var)
 elements_taptweak_curve_helpers=Some (_secp256k1_ge_set_xo_var,f_secp256k1_ge_set_xo_var))
 by (vm_compute;reflexivity).
 apply find_some in Found;exact (proj1 Found).
Qed.
Local Opaque elements_taptweak_ge secp_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_curve_entries id f:In (id,f) elements_taptweak_curve_helpers ->
 exists b1 b2,Genv.find_symbol secp_ge id=Some b1 /\Genv.find_funct_ptr secp_ge b1=Some(Internal f) /\
 Genv.find_symbol elements_taptweak_ge id=Some b2 /\Genv.find_funct_ptr elements_taptweak_ge b2=Some(Internal f).
Proof.
 intro Member.
 destruct (secp_helper_lookup_exists secp_ge id f
 (secp_map_eq_in _ _ _ elements_taptweak_curve_source_lookup (id,f) Member)) as (b1 & S1 & F1).
 destruct (secp_helper_lookup_exists elements_taptweak_ge id f
 (secp_map_eq_in _ _ _ elements_taptweak_curve_target_lookup (id,f) Member)) as (b2 & S2 & F2).
 exists b1,b2;repeat split;assumption.
Qed.
Lemma elements_taptweak_curve_ok id f:In (id,f) elements_taptweak_curve_helpers ->
 locals_fundef_okb secp_ge elements_taptweak_ge (map fst elements_taptweak_curve_helpers) (Internal f)=true.
Proof.
 intro Member;pose proof elements_taptweak_curve_closed as Checked.
 rewrite forallb_forall in Checked;exact (Checked (id,f) Member).
Qed.
Theorem elements_taptweak_curve_transport id f m args trace mf result:
 In (id,f) elements_taptweak_curve_helpers ->
 Clight2.eval_funcall secp_ge m (Internal f) args trace mf result ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f) args trace mf result.
Proof.
 intros Member Run;exact (locals_transport_funcall secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok id f Member m args trace mf result Run).
Qed.
