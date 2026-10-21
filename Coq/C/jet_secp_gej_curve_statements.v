(** Exact original projective checker statement tree and actual call nodes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_gej_infinity_layout.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_curve_helper_env b_y bx bz := PTree.set _z6 (bz,curve_fe_type)
  (PTree.set _y2 (b_y,curve_fe_type) (PTree.set _x3 (bx,curve_fe_type) empty_env)).
Definition gej_curve_field_address fid := Eaddrof
  (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) fid curve_fe_type) (tptr curve_fe_type).
Definition gej_curve_square_stmt dest fid := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address dest;gej_curve_field_address fid].
Definition gej_curve_mul_stmt dest fid := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address dest;curve_local_address dest;gej_curve_field_address fid].
Definition gej_curve_square_z_stmt := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _z6;curve_local_address _z6].
Definition gej_curve_mul7_stmt := curve_call _secp256k1_fe_mul_int f_secp256k1_fe_mul_int None
  [curve_local_address _z6;Econst_int (Int.repr 7) tint].
Definition gej_curve_add_stmt := curve_call _secp256k1_fe_add f_secp256k1_fe_add None
  [curve_local_address _x3;curve_local_address _z6].
Definition gej_curve_helper_stmt := fold_right Ssequence (Sreturn (Some (Etempvar _t'1 tint)))
  [gej_curve_square_stmt _y2 _y;gej_curve_square_stmt _x3 _x;gej_curve_mul_stmt _x3 _x;
   gej_curve_square_stmt _z6 _z;gej_curve_mul_stmt _z6 _z;gej_curve_square_z_stmt;
   gej_curve_mul7_stmt;gej_curve_add_stmt;curve_equal_statement].

Lemma gej_curve_helper_source : fn_body f_simplicity_gej_is_valid_var=gej_curve_helper_stmt.
Proof. reflexivity. Qed.

Lemma eval_gej_curve_field_address e le m ba fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> le!_a=Some (Vptr ba Ptrofs.zero) ->
  eval_expr secp_ge e le m (gej_curve_field_address fid) (Vptr ba (Ptrofs.repr delta)).
Proof.
  intros H HA.
  assert (HF : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
  { destruct H as [H|[H|[H|H]]];[left|right;left|right;right;left|contradiction];exact H. }
  destruct (gej_infinity_field_layout fid delta HF) as (co & HC & HO).
  unfold gej_curve_field_address;apply eval_Eaddrof.
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co:=co) (delta:=delta).
  - eapply eval_Elvalue.
    + apply eval_Ederef;apply eval_Etempvar;exact HA.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Local Ltac gej_curve_args HA :=
  first [apply eval_Enil |
    eapply eval_Econs;
      [first [apply eval_curve_local;reflexivity |
        apply eval_gej_curve_field_address;[cbn [In];tauto|exact HA] | constructor]
      |reflexivity|gej_curve_args HA]].
Local Ltac gej_curve_call HA HC :=
  lazymatch type of HC with
  | Clight2.eval_funcall _ _ _ ?call_args _ _ ?call_value =>
      eapply exec_curve_call with (vargs:=call_args) (v:=call_value);
        [unfold secp_pure;repeat (first [left;reflexivity|right]) |
         reflexivity | gej_curve_args HA | exact HC]
  end.

Theorem exec_gej_curve_from_calls le m m1 m2 m3 m4 m5 m6 m7 m8 mf ba b_y bx bz v :
  le!_a=Some (Vptr ba Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef ->
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef ->
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef ->
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m4 Vundef ->
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_mul)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m5 Vundef ->
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m6 Vundef ->
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul_int)
    [Vptr bz Ptrofs.zero;Vint (Int.repr 7)] E0 m7 Vundef ->
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_add)
    [Vptr bx Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m8 Vundef ->
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf (Vint v) ->
  Clight2.exec_stmt secp_ge (gej_curve_helper_env b_y bx bz) le m gej_curve_helper_stmt E0
    (PTree.set _t'1 (Vint v) le) mf (Out_return (Some (Vint v,tint))).
Proof.
  intros HA C1 C2 C3 C4 C5 C6 C7 C8 C9.
  unfold gej_curve_helper_stmt;cbn [fold_right].
  unfold gej_curve_square_stmt,gej_curve_mul_stmt,gej_curve_square_z_stmt,
    gej_curve_mul7_stmt,gej_curve_add_stmt,curve_equal_statement.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[gej_curve_call HA C1|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[gej_curve_call HA C2|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);[gej_curve_call HA C3|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);[gej_curve_call HA C4|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=le);[gej_curve_call HA C5|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m6) (le1:=le);[gej_curve_call HA C6|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m7) (le1:=le);[gej_curve_call HA C7|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m8) (le1:=le);[gej_curve_call HA C8|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint v) le);
    [gej_curve_call HA C9|].
  apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.
