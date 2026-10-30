(** Exact original x-only public-key parser's post-field-parse statements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Cop.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_root_chain_owned C.jet_secp_decompress_literal
 C.jet_secp_affine_storage C.jet_secp_storage_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress.
Definition xonly_parse_pk_address:=Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type).
Definition xonly_parse_x_address:=Eaddrof (Evar _x curve_fe_type) (tptr curve_fe_type).
Definition xonly_parse_guard id:=Sifthenelse (Eunop Onotbool (Etempvar id tint) tint)
 (Sreturn (Some (Econst_int Int.zero tint))) Sskip.
Definition xonly_parse_decode:=curve_call _secp256k1_ge_set_xo_var f_secp256k1_ge_set_xo_var (Some _t'2)
 [xonly_parse_pk_address;xonly_parse_x_address;Econst_int Int.zero tint].
Definition xonly_parse_subgroup:=curve_call _secp256k1_ge_is_in_correct_subgroup f_secp256k1_ge_is_in_correct_subgroup (Some _t'3)
 [xonly_parse_pk_address].
Definition xonly_parse_save:=curve_call _secp256k1_xonly_pubkey_save f_secp256k1_xonly_pubkey_save None
 [Etempvar _pubkey (tptr (Tstruct __6478 noattr));xonly_parse_pk_address].
Definition xonly_parse_after_decode:=Ssequence (Ssequence xonly_parse_subgroup (xonly_parse_guard _t'3))
 (Ssequence xonly_parse_save (Sreturn (Some (Econst_int Int.one tint)))).
Definition xonly_parse_decode_return:=Ssequence (Ssequence xonly_parse_decode (xonly_parse_guard _t'2)) xonly_parse_after_decode.
Lemma xonly_parse_decode_return_source:
 root_drop_statements 4 (fn_body f_secp256k1_xonly_pubkey_parse)=xonly_parse_decode_return.
Proof. reflexivity. Qed.
Definition xonly_decode_result (pk:Ty.tySem (Word 8)):=
 match @literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk) with
 |inl _=>Int.zero|inr _=>Int.one end.
Definition xonly_saved_result (pk:Ty.tySem (Word 8)) m b:=forall ax ay,
 @literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk)=inr (ax,ay) ->
 exists storage,affine_storage_readable m b 0 storage /\
 field_storage_value storage=@toZ (WordToZ 8) ax /\
 field_storage_value (fun i=>storage (4+i)%nat)=@toZ (WordToZ 8) ay.
Lemma exec_xonly_guard_one e le m id:le!id=Some (Vint Int.one) ->
 Clight2.exec_stmt secp_ge e le m (xonly_parse_guard id) E0 le m Out_normal.
Proof.
 intro Temp;unfold xonly_parse_guard;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
 - eapply eval_Eunop;[apply eval_Etempvar;exact Temp|reflexivity].
 - reflexivity.
 - constructor.
Qed.
Lemma exec_xonly_guard_zero e le m id:le!id=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge e le m (xonly_parse_guard id) E0 le m
 (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intro Temp;unfold xonly_parse_guard;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
 - eapply eval_Eunop;[apply eval_Etempvar;exact Temp|reflexivity].
 - reflexivity.
 - apply exec_Sreturn_some;constructor.
Qed.
Theorem eval_xonly_correct_subgroup m point:
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_in_correct_subgroup)
 [point] E0 m (Vint Int.one).
Proof.
 pose (le:=PTree.set _ge point (PTree.empty val)).
 assert (Entry:function_entry2 secp_ge f_secp256k1_ge_is_in_correct_subgroup [point] m empty_env le m).
 { assert (Ok:fn_okb f_secp256k1_ge_is_in_correct_subgroup=true) by reflexivity.
   destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity]. }
 eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=m)
 (out:=Out_return (Some (Vint Int.one,tint))).
 - exact Entry.
 - apply exec_Sreturn_some;constructor.
 - split;[discriminate|reflexivity].
 - reflexivity.
Qed.
