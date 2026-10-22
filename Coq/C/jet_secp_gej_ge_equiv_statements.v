(** Original projective/affine equivalence helper: exact statement tree and
    typed adapters. The three call premises are discharged by its caller proof. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_ge_equiv_env bt := PTree.set _tmp (bt,Tstruct __6123 noattr) empty_env.
Definition gej_ge_equiv_tmp_address := Eaddrof (Evar _tmp (Tstruct __6123 noattr))
 (tptr (Tstruct __6123 noattr)).
Definition gej_ge_equiv_negate_stmt := curve_call _secp256k1_gej_neg f_secp256k1_gej_neg None
 [gej_ge_equiv_tmp_address;Etempvar _a (tptr (Tstruct __6123 noattr))].
Definition gej_ge_equiv_add_stmt := curve_call _secp256k1_gej_add_ge_var f_secp256k1_gej_add_ge_var None
 [gej_ge_equiv_tmp_address;gej_ge_equiv_tmp_address;Etempvar _b (tptr (Tstruct __6121 noattr));
  Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Definition gej_ge_equiv_flag_stmt := curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity
 (Some _t'1) [gej_ge_equiv_tmp_address].
Definition gej_ge_equiv_body := Ssequence gej_ge_equiv_negate_stmt (Ssequence gej_ge_equiv_add_stmt
 (Ssequence gej_ge_equiv_flag_stmt (Sreturn (Some (Etempvar _t'1 tint))))).

Lemma gej_ge_equiv_body_source : fn_body f_secp256k1_gej_eq_ge_var=gej_ge_equiv_body.
Proof. reflexivity. Qed.

Local Ltac helper_member := unfold secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac helper_args HA HB := first [apply eval_Enil |
 eapply eval_Econs;
 [first [apply eval_Eaddrof;apply eval_Evar_local;reflexivity |
         apply eval_Etempvar;exact HA | apply eval_Etempvar;exact HB |
         eapply eval_Ecast with (v1:=Vint Int.zero);[constructor|reflexivity]] |
  reflexivity | helper_args HA HB]].

Theorem exec_gej_ge_equiv_body_from_calls le m mn ma bt bp ba flag :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_neg)
  [Vptr bt Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_gej_add_ge_var)
  [Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 ma Vundef ->
 Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_gej_is_infinity)
  [Vptr bt Ptrofs.zero] E0 ma (Vint flag) ->
 Clight2.exec_stmt secp_ge (gej_ge_equiv_env bt) le m (fn_body f_secp256k1_gej_eq_ge_var) E0
  (PTree.set _t'1 (Vint flag) le) ma (Out_return (Some (Vint flag,tint))).
Proof.
 intros HA HB Neg Add Flag;rewrite gej_ge_equiv_body_source;unfold gej_ge_equiv_body.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
 - unfold gej_ge_equiv_negate_stmt;eapply exec_curve_call with
    (vargs:=[Vptr bt Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
   + helper_member.
   + reflexivity.
   + unfold gej_ge_equiv_tmp_address;helper_args HA HB.
   + exact Neg.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=le).
   + unfold gej_ge_equiv_add_stmt;eapply exec_curve_call with
      (vargs:=[Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
     * helper_member.
     * reflexivity.
     * unfold gej_ge_equiv_tmp_address;helper_args HA HB.
     * exact Add.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=PTree.set _t'1 (Vint flag) le).
     * unfold gej_ge_equiv_flag_stmt;eapply exec_curve_call with (vargs:=[Vptr bt Ptrofs.zero]) (v:=Vint flag).
       -- helper_member.
       -- reflexivity.
       -- unfold gej_ge_equiv_tmp_address;helper_args HA HB.
       -- exact Flag.
     * apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.
