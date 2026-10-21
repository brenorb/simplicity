(** Exact original NULL-rzr dispatch, separated from arithmetic and storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_double_statements C.jet_secp_double_flag.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_var_null_test := Ebinop Cop.One (Etempvar _rzr (tptr curve_fe_type))
  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint.
Definition double_var_head := match fn_body f_secp256k1_gej_double_var with
  | Ssequence h _ => h | _ => Sskip end.
Definition double_var_tail := match fn_body f_secp256k1_gej_double_var with
  | Ssequence _ t => t | _ => Sskip end.
Lemma double_var_source : fn_body f_secp256k1_gej_double_var =
  Ssequence double_var_head double_var_tail.
Proof. reflexivity. Qed.
Lemma eval_double_var_null_test e le m : le!_rzr=Some (Vlong Int64.zero) ->
  eval_expr secp_ge e le m double_var_null_test (Vint Int.zero).
Proof.
  intro HR;unfold double_var_null_test.
  eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vlong Int64.zero).
  - apply eval_Etempvar;exact HR.
  - eapply eval_Ecast with (v1:=Vint Int.zero);[constructor|reflexivity].
  - reflexivity.
Qed.

Lemma exec_double_var_head_finite e le m ba :
  le!_a=Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
  Clight2.exec_stmt secp_ge e le m double_var_head E0
    (PTree.set _t'2 (Vint Int.zero) le) m Out_normal.
Proof.
  intros HA HF;unfold double_var_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vint Int.zero) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint Int.zero));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Lemma exec_double_var_tail_from_calls e le m md mz mf ba flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_rzr=Some (Vlong Int64.zero) ->
  e!_secp256k1_gej_double=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 md Vundef ->
  Clight2.eval_funcall secp_ge md (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr ba (Ptrofs.repr 80)] E0 mz (Vint flag) ->
  Mem.store Mint32 mz ba 120 (Vint flag)=Some mf ->
  Clight2.exec_stmt secp_ge e le m double_var_tail E0
    (PTree.set _t'1 (Vint flag) le) mf Out_normal.
Proof.
  intros HA HR HN HD HZ CD CZ HS;unfold double_var_tail.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_double_var_null_test;exact HN.
    + reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le).
    + change (Clight2.exec_stmt secp_ge e le m
        (curve_call _secp256k1_gej_double f_secp256k1_gej_double None
          [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _a (tptr (Tstruct __6123 noattr))]) E0 le md Out_normal).
      eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef);
        [unfold secp_pure;repeat (first [left;reflexivity|right])|exact HD| |exact CD].
      eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
      eapply eval_Econs;[apply eval_Etempvar;exact HA|reflexivity|constructor].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint flag) le).
      * change (Clight2.exec_stmt secp_ge e le md
          (curve_call _secp256k1_fe_normalizes_to_zero_var f_secp256k1_fe_normalizes_to_zero_var (Some _t'1)
            [double_point_address _r _z]) E0 (PTree.set _t'1 (Vint flag) le) mz Out_normal).
        eapply exec_curve_call with (vargs:=[Vptr ba (Ptrofs.repr 80)]) (v:=Vint flag);
          [unfold secp_pure;repeat (first [left;reflexivity|right])|exact HZ| |exact CZ].
        eapply eval_Econs;[apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|constructor].
      * eapply exec_Sassign with (loc:=ba) (ofs:=Ptrofs.repr 120) (bf:=Full)
          (v2:=Vint flag) (v:=Vint flag).
        -- apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
        -- apply eval_Etempvar;apply PTree.gss.
        -- reflexivity.
        -- eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
           change (Mem.store Mint32 mz ba 120 (Vint flag)=Some mf);exact HS.
Qed.

Lemma exec_double_var_head_infinite e le m mf ba flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_rzr=Some (Vlong Int64.zero) -> e!_secp256k1_gej_set_infinity=None ->
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_infinity)
    [Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m double_var_head E0
    (PTree.set _t'2 (Vint flag) le) mf (Out_return None).
Proof.
  intros HA HR HN HE HF HFlag HC;unfold double_var_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint flag));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
    + apply eval_Etempvar;apply PTree.gss.
    + change (Some (negb (Int.eq flag Int.zero))=Some true).
      rewrite Int.eq_false by exact HFlag;reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'2 (Vint flag) le).
      * change (Clight2.exec_stmt secp_ge e (PTree.set _t'2 (Vint flag) le) m
          (curve_call _secp256k1_gej_set_infinity f_secp256k1_gej_set_infinity None
            [Etempvar _r (tptr (Tstruct __6123 noattr))]) E0 (PTree.set _t'2 (Vint flag) le) mf Out_normal).
        eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero]) (v:=Vundef);
          [unfold secp_pure;repeat (first [left;reflexivity|right])|exact HE| |exact HC].
        eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HR|reflexivity|constructor].
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'2 (Vint flag) le).
        -- eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
           ++ apply eval_double_var_null_test;rewrite PTree.gso by discriminate;exact HN.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- apply exec_Sreturn_none.
Qed.
