(** Exact original X-equivalence helper body and its call interfaces. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_gej_infinity_layout C.jet_secp_curve_statements C.jet_secp_x_equiv_copy.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition x_equiv_helper_env br br2 :=
  PTree.set _r2 (br2,curve_fe_type) (PTree.set _r (br,curve_fe_type) empty_env).
Definition x_equiv_z_address := Eaddrof
  (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) _z curve_fe_type) (tptr curve_fe_type).
Definition x_equiv_square_stmt := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _r;x_equiv_z_address].
Definition x_equiv_multiply_stmt := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _r;curve_local_address _r;Etempvar _x (tptr curve_fe_type)].
Definition x_equiv_weak_stmt := curve_call _secp256k1_fe_normalize_weak f_secp256k1_fe_normalize_weak None
  [curve_local_address _r2].
Definition x_equiv_equal_stmt := curve_call _secp256k1_fe_equal_var f_secp256k1_fe_equal_var (Some _t'1)
  [curve_local_address _r;curve_local_address _r2].
Definition x_equiv_helper_stmt := Ssequence (Sloop Sskip Sbreak)
  (Ssequence x_equiv_square_stmt (Ssequence x_equiv_multiply_stmt
    (Ssequence x_equiv_copy_stmt (Ssequence x_equiv_weak_stmt
      (Ssequence x_equiv_equal_stmt (Sreturn (Some (Etempvar _t'1 tint)))))))).

Lemma x_equiv_helper_body_source : fn_body f_secp256k1_gej_eq_x_var = x_equiv_helper_stmt.
Proof. reflexivity. Qed.

Lemma eval_x_equiv_z_address e le m bp : le!_a = Some (Vptr bp Ptrofs.zero) ->
  eval_expr secp_ge e le m x_equiv_z_address (Vptr bp (Ptrofs.repr 80)).
Proof.
  intro HA. destruct (gej_infinity_field_layout _z 80 ltac:(right;right;left;reflexivity))
    as (co & HC & HO).
  unfold x_equiv_z_address. apply eval_Eaddrof.
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr 80)).
  eapply eval_Efield_struct with (co:=co) (delta:=80).
  - eapply eval_Elvalue.
    + apply eval_Ederef; apply eval_Etempvar;exact HA.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Local Ltac x_equiv_symbol :=
  unfold secp_pure; repeat (first [left;reflexivity|right]).
Local Ltac x_equiv_args HA HQ :=
  first [apply eval_Enil |
    eapply eval_Econs;
      [first [apply eval_curve_local;reflexivity |
              apply eval_x_equiv_z_address;exact HA |
              apply eval_Etempvar;exact HQ]
      |reflexivity|x_equiv_args HA HQ]].

Theorem exec_x_equiv_body_from_calls le m ms mm mc mn mf bp bq br br2 v :
  le!_a = Some (Vptr bp Ptrofs.zero) -> le!_x = Some (Vptr bq Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr br Ptrofs.zero;Vptr bp (Ptrofs.repr 80)] E0 ms Vundef ->
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_fe_mul)
    [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bq Ptrofs.zero] E0 mm Vundef ->
  Clight2.exec_stmt secp_ge (x_equiv_helper_env br br2) le mm x_equiv_copy_stmt E0 le mc Out_normal ->
  Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_fe_normalize_weak)
    [Vptr br2 Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_fe_equal_var)
    [Vptr br Ptrofs.zero;Vptr br2 Ptrofs.zero] E0 mf (Vint v) ->
  Clight2.exec_stmt secp_ge (x_equiv_helper_env br br2) le m x_equiv_helper_stmt E0
    (PTree.set _t'1 (Vint v) le) mf (Out_return (Some (Vint v,tint))).
Proof.
  intros HA HQ CS CM CC CN CE. unfold x_equiv_helper_stmt.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
  - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
      (out1:=Out_normal); constructor.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
    + unfold x_equiv_square_stmt. eapply exec_curve_call with
        (vargs:=[Vptr br Ptrofs.zero;Vptr bp (Ptrofs.repr 80)]) (v:=Vundef).
      * x_equiv_symbol.
      * reflexivity.
      * x_equiv_args HA HQ.
      * exact CS.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mm) (le1:=le).
      * unfold x_equiv_multiply_stmt. eapply exec_curve_call with
          (vargs:=[Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bq Ptrofs.zero]) (v:=Vundef).
        -- x_equiv_symbol.
        -- reflexivity.
        -- x_equiv_args HA HQ.
        -- exact CM.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
        -- exact CC.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
           ++ unfold x_equiv_weak_stmt. eapply exec_curve_call with
                (vargs:=[Vptr br2 Ptrofs.zero]) (v:=Vundef).
              ** x_equiv_symbol.
              ** reflexivity.
              ** x_equiv_args HA HQ.
              ** exact CN.
           ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
                (le1:=PTree.set _t'1 (Vint v) le).
              ** unfold x_equiv_equal_stmt. eapply exec_curve_call with
                   (vargs:=[Vptr br Ptrofs.zero;Vptr br2 Ptrofs.zero]) (v:=Vint v).
                 --- x_equiv_symbol.
                 --- reflexivity.
                 --- x_equiv_args HA HQ.
                 --- exact CE.
              ** apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.
Print Assumptions exec_x_equiv_body_from_calls.
