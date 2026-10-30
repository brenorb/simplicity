(** Exact original x-only public-key parser's post-field-parse statements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Cop Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_root_chain_owned C.jet_secp_decompress_literal
 C.jet_secp_affine_storage C.jet_secp_storage_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_xonly_parse_control.
Section ParseControl.
Variable ge:Clight.genv.
Lemma exec_curve_call_at id fd result args vargs v e le m mf bf:
 Genv.find_symbol ge id=Some bf ->
 Genv.find_funct ge (Vptr bf Ptrofs.zero)=Some (Internal fd) ->e!id=None ->
 eval_exprlist ge e le m args (type_of_params (fn_params fd)) vargs ->
 Clight2.eval_funcall ge m (Internal fd) vargs E0 mf v ->
 Clight2.exec_stmt ge e le m (curve_call id fd result args) E0 (set_opttemp result v le) mf Out_normal.
Proof.
 intros Symbol Function Global Args Call;unfold curve_call.
 eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero) (vargs:=vargs) (f:=Internal fd) (vres:=v).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact Symbol]|apply deref_loc_reference;reflexivity].
 - exact Args.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Lemma exec_xonly_guard_one_at e le m id:le!id=Some (Vint Int.one) ->
 Clight2.exec_stmt ge e le m (xonly_parse_guard id) E0 le m Out_normal.
Proof.
 intro Temp;unfold xonly_parse_guard;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
 - eapply eval_Eunop;[apply eval_Etempvar;exact Temp|reflexivity].
 - reflexivity.
 - constructor.
Qed.
Lemma exec_xonly_guard_zero_at e le m id:le!id=Some (Vint Int.zero) ->
 Clight2.exec_stmt ge e le m (xonly_parse_guard id) E0 le m
 (Out_return (Some (Vint Int.zero,tint))).
Proof.
 intro Temp;unfold xonly_parse_guard;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
 - eapply eval_Eunop;[apply eval_Etempvar;exact Temp|reflexivity].
 - reflexivity.
 - apply exec_Sreturn_some;constructor.
Qed.
Theorem eval_xonly_correct_subgroup_at m point:
 Clight2.eval_funcall ge m (Internal f_secp256k1_ge_is_in_correct_subgroup)
 [point] E0 m (Vint Int.one).
Proof.
 pose (le:=PTree.set _ge point (PTree.empty val)).
 assert (Entry:function_entry2 ge f_secp256k1_ge_is_in_correct_subgroup [point] m empty_env le m).
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
End ParseControl.
