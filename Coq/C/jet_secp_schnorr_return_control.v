(** Exact original Schnorr normalization/parity/equality/return control.
    Helper executions are intermediate premises, to be composed by the caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_root_chain_owned.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_result_field fid:=Efield (Evar _r curve_ge_type) fid curve_fe_type.
Definition schnorr_result_address fid:=Eaddrof (schnorr_result_field fid) (tptr curve_fe_type).
Definition schnorr_return_normalize:=curve_call _secp256k1_fe_normalize_var f_secp256k1_fe_normalize_var None
 [schnorr_result_address _y].
Definition schnorr_return_odd:=curve_call _secp256k1_fe_is_odd f_secp256k1_fe_is_odd (Some _t'5)
 [schnorr_result_address _y].
Definition schnorr_return_equal:=curve_call _secp256k1_fe_equal_var f_secp256k1_fe_equal_var (Some _t'7)
 [Eaddrof (Evar _rx curve_fe_type) (tptr curve_fe_type);schnorr_result_address _x].
Definition schnorr_return_cond:=Sifthenelse (Eunop Onotbool (Etempvar _t'5 tint) tint)
 (Ssequence schnorr_return_equal (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool)))
 (Sset _t'6 (Econst_int Int.zero tint)).
Definition schnorr_return_tail:=Ssequence schnorr_return_normalize
 (Ssequence (Ssequence schnorr_return_odd schnorr_return_cond) (Sreturn (Some (Etempvar _t'6 tint)))).
Lemma schnorr_return_source:root_drop_statements 14 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_return_tail.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Lemma eval_schnorr_result_address e le m br fid delta:
 In (fid,delta) [(_x,0);(_y,40)] ->e!_r=Some (br,curve_ge_type) ->
 eval_expr secp_ge e le m (schnorr_result_address fid) (Vptr br (Ptrofs.repr delta)).
Proof.
 intros Field LocalR;destruct (curve_affine_layout fid delta ltac:(cbn [In] in *;tauto)) as [co [Layout Offset]].
 apply eval_Eaddrof;unfold schnorr_result_field.
 rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Evar_local;exact LocalR|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Layout.
 - exact Offset.
Qed.
Definition schnorr_return_temps le (odd equal:bool):=
 let li:=PTree.set _t'5 (Vint (bit_int odd)) le in
 if odd then PTree.set _t'6 (Vint Int.zero) li
 else PTree.set _t'6 (Vint (bit_int equal)) (PTree.set _t'7 (Vint (bit_int equal)) li).
Theorem exec_schnorr_return_from_calls e le m mn mo me br bx (odd equal:bool):
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var)
  [Vptr br (Ptrofs.repr 40)] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_fe_is_odd)
  [Vptr br (Ptrofs.repr 40)] E0 mo (Vint (bit_int odd)) ->
 (odd=false ->Clight2.eval_funcall secp_ge mo (Internal f_secp256k1_fe_equal_var)
  [Vptr bx Ptrofs.zero;Vptr br Ptrofs.zero] E0 me (Vint (bit_int equal))) ->
 Clight2.exec_stmt secp_ge e le m schnorr_return_tail E0
 (schnorr_return_temps le odd equal) (if odd then mo else me)
 (Out_return (Some (Vint (bit_int (andb (negb odd) equal)),tint))).
Proof.
 intros LocalR LocalX NormSym OddSym EqSym Normalize Odd Equal.
 assert (NormRun:Clight2.exec_stmt secp_ge e le m schnorr_return_normalize E0 le mn Out_normal).
 { unfold schnorr_return_normalize;eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr 40)]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact NormSym.
   - eapply eval_Econs;[apply eval_schnorr_result_address;[cbn [In];tauto|exact LocalR]|reflexivity|constructor].
   - exact Normalize. }
 assert (OddRun:Clight2.exec_stmt secp_ge e le mn schnorr_return_odd E0
  (PTree.set _t'5 (Vint (bit_int odd)) le) mo Out_normal).
 { unfold schnorr_return_odd;eapply exec_curve_call with (vargs:=[Vptr br (Ptrofs.repr 40)]) (v:=Vint (bit_int odd)).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact OddSym.
   - eapply eval_Econs;[apply eval_schnorr_result_address;[cbn [In];tauto|exact LocalR]|reflexivity|constructor].
   - exact Odd. }
 unfold schnorr_return_tail;destruct odd.
 - unfold schnorr_return_temps;cbn [negb andb bit_int].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le);[exact NormRun|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mo)
    (le1:=PTree.set _t'6 (Vint Int.zero) (PTree.set _t'5 (Vint Int.one) le)).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mo)
     (le1:=PTree.set _t'5 (Vint Int.one) le);[exact OddRun|].
     unfold schnorr_return_cond;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * reflexivity.
     * apply exec_Sset;constructor.
   + apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
 - unfold schnorr_return_temps;cbn [negb andb].
   set (li:=PTree.set _t'5 (Vint (bit_int false)) le).
   assert (EqRun:Clight2.exec_stmt secp_ge e li mo schnorr_return_equal E0
    (PTree.set _t'7 (Vint (bit_int equal)) li) me Out_normal).
   { unfold schnorr_return_equal;eapply exec_curve_call with
     (vargs:=[Vptr bx Ptrofs.zero;Vptr br Ptrofs.zero]) (v:=Vint (bit_int equal)).
     - unfold secp_pure;repeat first [left;reflexivity|right].
     - exact EqSym.
     - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact LocalX|reflexivity|].
       eapply eval_Econs;[apply eval_schnorr_result_address;[cbn [In];tauto|exact LocalR]|reflexivity|constructor].
     - apply Equal;reflexivity. }
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le);[exact NormRun|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=me)
    (le1:=PTree.set _t'6 (Vint (bit_int equal)) (PTree.set _t'7 (Vint (bit_int equal)) li)).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mo) (le1:=li);[exact OddRun|].
     unfold schnorr_return_cond;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=me)
       (le1:=PTree.set _t'7 (Vint (bit_int equal)) li);[exact EqRun|].
       apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|destruct equal;reflexivity].
   + apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.
