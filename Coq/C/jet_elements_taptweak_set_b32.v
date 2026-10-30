(** Reuse the original strict field parser with the exact same memory effect
    in the linked Elements program, retaining both success and rejection. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Globalenvs Memory Values Events.
Require Import C.jet_transport C.jet_secp_linkage C.jets_secp C.jet_sx_mem
 C.jet_elements_taptweak_pure C.jet_secp_set_b32_owned C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_generator_load_values
 C.jet_secp_xonly_parse_field C.jet_secp_swu_raw_input C.jet_secp_root_chain_owned
 C.jet_read8s_layout C.jet_clight_internal_preserve C.jet_sx_zval C.jet_secp_multiply_normalize_bridge.
Require Import Simplicity.Ty Simplicity.Word.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_b32_helpers:=[(_secp256k1_fe_set_b32,f_secp256k1_fe_set_b32)].
Lemma elements_taptweak_b32_lookup_source:
 secp_helper_lookup secp_ge (_secp256k1_fe_set_b32,f_secp256k1_fe_set_b32)=Some (Internal f_secp256k1_fe_set_b32).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_b32_lookup_target:
 secp_helper_lookup elements_taptweak_ge (_secp256k1_fe_set_b32,f_secp256k1_fe_set_b32)=Some (Internal f_secp256k1_fe_set_b32).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_b32_checked:
 fundef_okb secp_ge elements_taptweak_ge (map fst elements_taptweak_b32_helpers)
 (Internal f_secp256k1_fe_set_b32)=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma elements_taptweak_b32_entries id f:In (id,f) elements_taptweak_b32_helpers ->
 exists b1 b2,Genv.find_symbol secp_ge id=Some b1 /\Genv.find_funct_ptr secp_ge b1=Some (Internal f) /\
 Genv.find_symbol elements_taptweak_ge id=Some b2 /\Genv.find_funct_ptr elements_taptweak_ge b2=Some (Internal f).
Proof.
 intros [Same|[]];injection Same as <- <-.
 destruct (secp_helper_lookup_exists secp_ge _ _ elements_taptweak_b32_lookup_source) as (b1 & S1 & F1).
 destruct (secp_helper_lookup_exists elements_taptweak_ge _ _ elements_taptweak_b32_lookup_target) as (b2 & S2 & F2).
 exists b1,b2;repeat split;assumption.
Qed.
Lemma elements_taptweak_b32_ok id f:In (id,f) elements_taptweak_b32_helpers ->
 fundef_okb secp_ge elements_taptweak_ge (map fst elements_taptweak_b32_helpers) (Internal f)=true.
Proof. intros [Same|[]];injection Same as <- <-;exact elements_taptweak_b32_checked. Qed.
Theorem elements_taptweak_b32_transport m args trace mf result:
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32) args trace mf result ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_fe_set_b32) args trace mf result.
Proof.
 intro Run;exact (transport_funcall secp_ge elements_taptweak_ge elements_taptweak_b32_helpers
 elements_taptweak_b32_entries elements_taptweak_b32_ok _ _ ltac:(left;reflexivity) m args trace mf result Run).
Qed.
Theorem eval_elements_taptweak_set_b32_owned bytes m bt bb:
 length bytes=32%nat ->Forall (fun x=>0<=x<=255) bytes ->bt<>bb ->
 Mem.range_perm m bt 0 40 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
 exists mf,Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_fe_set_b32)
 [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (Int.repr (b2z (Z.ltb (be_val bytes) feP)))) /\
 fe_at mf bt 0 (map Int64.repr (fe_limbs_of (be_val bytes))) /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) /\
 lframe (fun b _=>b<>bt /\b<>bb) m mf /\readonly_preserved m mf.
Proof.
 intros Len Bytes Sep FT FB Loads.
 destruct (eval_set_b32_owned bytes m bt bb Len Bytes Sep FT FB Loads) as (mf & Call & Memory).
 exists mf;split;[exact (elements_taptweak_b32_transport _ _ _ _ _ Call)|exact Memory].
Qed.
Theorem eval_elements_taptweak_xonly_field_read pk m bx bin:
 bx<>bin ->Mem.range_perm m bx 0 40 Cur Freeable ->Mem.range_perm m bin 0 32 Cur Freeable ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_fe_set_b32)
 [Vptr bx Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint (xonly_strict_flag pk)) /\
 fe_at mf bx 0 (words5 (swu_raw_words pk)) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\Mem.range_perm mf bin 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bx /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros Sep FX FB Input.
 destruct (eval_xonly_field_read pk m bx bin Sep FX FB Input) as (mf & Call & Memory).
 exists mf;split;[exact (elements_taptweak_b32_transport _ _ _ _ _ Call)|exact Memory].
Qed.
