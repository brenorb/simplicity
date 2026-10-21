(** Exact generated doubling statement tree and execution of its arithmetic
    suffix from the original helper calls.  The caller discharges those calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_gej_infinity_layout.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_helper_env bl bs bt := PTree.set _t (bt,curve_fe_type)
  (PTree.set _s (bs,curve_fe_type) (PTree.set _l (bl,curve_fe_type) empty_env)).
Definition double_point_field p fid ty := Efield
  (Ederef (Etempvar p (tptr (Tstruct __6123 noattr))) (Tstruct __6123 noattr)) fid ty.
Definition double_point_address p fid := Eaddrof (double_point_field p fid curve_fe_type) (tptr curve_fe_type).
Definition double_flag_stmt := Ssequence
  (Sset _t'1 (double_point_field _a _infinity tint))
  (Sassign (double_point_field _r _infinity tint) (Etempvar _t'1 tint)).
Definition double_arithmetic_body := fold_right Ssequence
  (curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
    [double_point_address _r _y;double_point_address _r _y;Econst_int (Int.repr 2) tint])
  [curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
     [double_point_address _r _z;double_point_address _a _z;double_point_address _a _y];
   curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
     [curve_local_address _s;double_point_address _a _y];
   curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
     [curve_local_address _l;double_point_address _a _x];
   curve_call _secp256k1_fe_mul_int f_secp256k1_fe_mul_int None
     [curve_local_address _l;Econst_int (Int.repr 3) tint];
   curve_call _secp256k1_fe_half f_secp256k1_fe_half None [curve_local_address _l];
   curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
     [curve_local_address _t;curve_local_address _s;Econst_int (Int.repr 1) tint];
   curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
     [curve_local_address _t;curve_local_address _t;double_point_address _a _x];
   curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
     [double_point_address _r _x;curve_local_address _l];
   curve_call _secp256k1_fe_add f_secp256k1_fe_add None
     [double_point_address _r _x;curve_local_address _t];
   curve_call _secp256k1_fe_add f_secp256k1_fe_add None
     [double_point_address _r _x;curve_local_address _t];
   curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None [curve_local_address _s;curve_local_address _s];
   curve_call _secp256k1_fe_add f_secp256k1_fe_add None [curve_local_address _t;double_point_address _r _x];
   curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
     [double_point_address _r _y;curve_local_address _t;curve_local_address _l];
   curve_call _secp256k1_fe_add f_secp256k1_fe_add None [double_point_address _r _y;curve_local_address _s]].

Lemma double_helper_source : fn_body f_secp256k1_gej_double=Ssequence double_flag_stmt double_arithmetic_body.
Proof. reflexivity. Qed.

Lemma eval_double_point_address e le m bp p fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> le!p=Some (Vptr bp Ptrofs.zero) ->
  eval_expr secp_ge e le m (double_point_address p fid) (Vptr bp (Ptrofs.repr delta)).
Proof.
  intros H HP.
  assert (HF : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]).
  { destruct H as [H|[H|[H|H]]];[left|right;left|right;right;left|contradiction];exact H. }
  destruct (gej_infinity_field_layout fid delta HF) as (co & HC & HO).
  unfold double_point_address,double_point_field;apply eval_Eaddrof.
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co:=co) (delta:=delta).
  - eapply eval_Elvalue.
    + apply eval_Ederef;apply eval_Etempvar;exact HP.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Local Ltac double_args HA HR :=
  first [apply eval_Enil |
    eapply eval_Econs;
      [first [apply eval_curve_local;reflexivity |
        apply eval_double_point_address;[cbn [In];tauto|first [exact HA|exact HR]] | constructor]
      |reflexivity|double_args HA HR]].
Local Ltac double_exec_call HA HR HC :=
  lazymatch type of HC with
  | Clight2.eval_funcall _ _ _ ?args _ _ ?value =>
      eapply exec_curve_call with (vargs:=args) (v:=value);
        [unfold secp_pure;repeat (first [left;reflexivity|right]) |
         reflexivity | double_args HA HR | exact HC]
  end.

Theorem exec_double_arithmetic_from_calls le m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 mf bp bs bl bt :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 40)] E0 m1 Vundef ->
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr bp (Ptrofs.repr 40)] E0 m2 Vundef ->
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
    [Vptr bl Ptrofs.zero;Vptr bp Ptrofs.zero] E0 m3 Vundef ->
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul_int)
    [Vptr bl Ptrofs.zero;Vint (Int.repr 3)] E0 m4 Vundef ->
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_half) [Vptr bl Ptrofs.zero] E0 m5 Vundef ->
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_negate)
    [Vptr bt Ptrofs.zero;Vptr bs Ptrofs.zero;Vint Int.one] E0 m6 Vundef ->
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul)
    [Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bp Ptrofs.zero] E0 m7 Vundef ->
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_sqr)
    [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m8 Vundef ->
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_add)
    [Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m9 Vundef ->
  Clight2.eval_funcall secp_ge m9 (Internal f_secp256k1_fe_add)
    [Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m10 Vundef ->
  Clight2.eval_funcall secp_ge m10 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero] E0 m11 Vundef ->
  Clight2.eval_funcall secp_ge m11 (Internal f_secp256k1_fe_add)
    [Vptr bt Ptrofs.zero;Vptr bp Ptrofs.zero] E0 m12 Vundef ->
  Clight2.eval_funcall secp_ge m12 (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m13 Vundef ->
  Clight2.eval_funcall secp_ge m13 (Internal f_secp256k1_fe_add)
    [Vptr bp (Ptrofs.repr 40);Vptr bs Ptrofs.zero] E0 m14 Vundef ->
  Clight2.eval_funcall secp_ge m14 (Internal f_secp256k1_fe_negate)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vint (Int.repr 2)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m double_arithmetic_body E0 le mf Out_normal.
Proof.
  intros HA HR C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15.
  unfold double_arithmetic_body;cbn [fold_right].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);[double_exec_call HA HR C1|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[double_exec_call HA HR C2|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le);[double_exec_call HA HR C3|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le);[double_exec_call HA HR C4|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=le);[double_exec_call HA HR C5|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m6) (le1:=le);[double_exec_call HA HR C6|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m7) (le1:=le);[double_exec_call HA HR C7|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m8) (le1:=le);[double_exec_call HA HR C8|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m9) (le1:=le);[double_exec_call HA HR C9|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m10) (le1:=le);[double_exec_call HA HR C10|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m11) (le1:=le);[double_exec_call HA HR C11|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m12) (le1:=le);[double_exec_call HA HR C12|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m13) (le1:=le);[double_exec_call HA HR C13|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m14) (le1:=le);[double_exec_call HA HR C14|].
  double_exec_call HA HR C15.
Qed.
