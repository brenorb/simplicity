(** Exact original curve-check statement tree, linkage, and argument addresses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs Errors.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_fe_type := Tstruct __5467 noattr.
Definition curve_ge_type := Tstruct __6121 noattr.
Definition curve_helper_env b_y2 b_x3 :=
  PTree.set _x3 (b_x3,curve_fe_type) (PTree.set _y2 (b_y2,curve_fe_type) empty_env).
Definition curve_local_address id := Eaddrof (Evar id curve_fe_type) (tptr curve_fe_type).
Definition curve_affine_field fid ty :=
  Efield (Ederef (Etempvar _a (tptr curve_ge_type)) curve_ge_type) fid ty.
Definition curve_field_address fid := Eaddrof (curve_affine_field fid curve_fe_type) (tptr curve_fe_type).
Definition curve_call id fd result args := Scall result (Evar id (type_of_function fd)) args.
Definition curve_square_statement (y : bool) :=
  curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
    [curve_local_address (if y then _y2 else _x3); curve_field_address (if y then _y else _x)].
Definition curve_mul_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _x3;curve_local_address _x3;curve_field_address _x].
Definition curve_add_statement := curve_call _secp256k1_fe_add_int f_secp256k1_fe_add_int None
  [curve_local_address _x3;Econst_int (Int.repr 7) tint].
Definition curve_weak_statement := curve_call _secp256k1_fe_normalize_weak f_secp256k1_fe_normalize_weak None
  [curve_local_address _x3].
Definition curve_equal_statement := curve_call _secp256k1_fe_equal_var f_secp256k1_fe_equal_var (Some _t'1)
  [curve_local_address _y2;curve_local_address _x3].
Definition curve_arithmetic_statement := Ssequence (curve_square_statement true)
  (Ssequence (curve_square_statement false) (Ssequence curve_mul_statement
    (Ssequence curve_add_statement (Ssequence curve_weak_statement
      (Ssequence curve_equal_statement (Sreturn (Some (Etempvar _t'1 tint)))))))).
Definition curve_flag_statement := Ssequence (Sset _t'2 (curve_affine_field _infinity tint))
  (Sifthenelse (Etempvar _t'2 tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip).

Lemma curve_valid_body_source : fn_body f_secp256k1_ge_is_valid_var =
  Ssequence curve_flag_statement curve_arithmetic_statement.
Proof. reflexivity. Qed.
Lemma curve_valid_object_sizes : sizeof (genv_cenv secp_ge) curve_fe_type = 40 /\
  sizeof (genv_cenv secp_ge) curve_ge_type = 88.
Proof. split; reflexivity. Qed.

Lemma curve_affine_layout fid delta : In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] ->
  exists co, (genv_cenv secp_ge)!__6121 = Some co /\
  field_offset secp_ge fid (co_members co) = OK (delta,Full).
Proof.
  intro H.
  assert (HM : option_map co_members ((genv_cenv secp_ge)!__6121) =
    Some [Member_plain _x curve_fe_type;Member_plain _y curve_fe_type;Member_plain _infinity tint])
    by (vm_compute; reflexivity).
  destruct ((genv_cenv secp_ge)!__6121) as [co|] eqn:HC; [|discriminate].
  exists co; split; [reflexivity|]. inversion HM as [HMembers]. rewrite HMembers.
  destruct H as [H|[H|[H|H]]]; [| | |contradiction]; inversion H; subst; vm_compute; reflexivity.
Qed.

Lemma eval_curve_field e le m ba fid delta ty :
  In (fid,delta) [(_x,0);(_y,40);(_infinity,80)] -> le!_a = Some (Vptr ba Ptrofs.zero) ->
  eval_lvalue secp_ge e le m (curve_affine_field fid ty) ba (Ptrofs.repr delta) Full.
Proof.
  intros H HA. destruct (curve_affine_layout fid delta H) as (co & HC & HO).
  unfold curve_affine_field. rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co := co) (delta := delta).
  - eapply eval_Elvalue.
    + apply eval_Ederef; apply eval_Etempvar; exact HA.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Lemma eval_curve_field_address e le m ba fid delta :
  In (fid,delta) [(_x,0);(_y,40)] -> le!_a = Some (Vptr ba Ptrofs.zero) ->
  eval_expr secp_ge e le m (curve_field_address fid) (Vptr ba (Ptrofs.repr delta)).
Proof.
  intros H HA. apply eval_Eaddrof. apply eval_curve_field; [|exact HA].
  destruct H as [H|[H|H]]; [left|right; left|contradiction]; exact H.
Qed.

Lemma eval_curve_local e le m b id : e!id = Some (b,curve_fe_type) ->
  eval_expr secp_ge e le m (curve_local_address id) (Vptr b Ptrofs.zero).
Proof. intro H. apply eval_Eaddrof. apply eval_Evar_local; exact H. Qed.

Lemma exec_curve_call id fd result args vargs v e le m mf :
  In (id,fd) secp_pure -> e!id = None ->
  eval_exprlist secp_ge e le m args (type_of_params (fn_params fd)) vargs ->
  Clight2.eval_funcall secp_ge m (Internal fd) vargs E0 mf v ->
  Clight2.exec_stmt secp_ge e le m (curve_call id fd result args)
    E0 (set_opttemp result v le) mf Out_normal.
Proof.
  intros HIn HE HArgs HCall. destruct (secp_pure_ok id fd HIn) as (bf & HS & HF).
  unfold curve_call. eapply exec_Scall with (vf := Vptr bf Ptrofs.zero) (vargs := vargs)
    (f := Internal fd) (vres := v).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HE|exact HS].
    + apply deref_loc_reference; reflexivity.
  - exact HArgs.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_curve_flag_finite le m ba b_y2 bx :
  le!_a = Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  Clight2.exec_stmt secp_ge (curve_helper_env b_y2 bx) le m curve_flag_statement E0
    (PTree.set _t'2 (Vint Int.zero) le) m Out_normal.
Proof.
  intros HA HF. unfold curve_flag_statement.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vint Int.zero) le).
  - apply exec_Sset. eapply eval_Elvalue.
    + apply eval_curve_field; [cbn [In]; tauto|exact HA].
    + eapply deref_loc_value with (chunk:=Mint32); [reflexivity|].
      change (Mem.load Mint32 m ba 80 = Some (Vint Int.zero)); exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar. apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Local Ltac curve_arguments HA :=
  first [apply eval_Enil |
    eapply eval_Econs;
      [first [apply eval_curve_local; reflexivity |
              apply eval_curve_field_address; [cbn [In]; tauto|exact HA] |
              constructor]
      |reflexivity|curve_arguments HA]].
Local Ltac curve_symbol :=
  unfold secp_pure; repeat (first [left; reflexivity|right]).

Theorem exec_curve_arithmetic_from_calls le m m1 m2 m3 m4 m5 mf ba b_y2 bx v :
  le!_a = Some (Vptr ba Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y2 Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef ->
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef ->
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef ->
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_add_int)
    [Vptr bx Ptrofs.zero;Vint (Int.repr 7)] E0 m4 Vundef ->
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_normalize_weak)
    [Vptr bx Ptrofs.zero] E0 m5 Vundef ->
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y2 Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf (Vint v) ->
  Clight2.exec_stmt secp_ge (curve_helper_env b_y2 bx) le m curve_arithmetic_statement E0
    (PTree.set _t'1 (Vint v) le) mf (Out_return (Some (Vint v,tint))).
Proof.
  intros HA C1 C2 C3 C4 C5 C6. unfold curve_arithmetic_statement.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
  - eapply exec_curve_call with (vargs:=[Vptr b_y2 Ptrofs.zero;Vptr ba (Ptrofs.repr 40)]) (v:=Vundef).
    + curve_symbol.
    + reflexivity.
    + curve_arguments HA.
    + exact C1.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
    + eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef).
      * curve_symbol.
      * reflexivity.
      * curve_arguments HA.
      * exact C2.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
      * eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vundef).
        -- curve_symbol.
        -- reflexivity.
        -- curve_arguments HA.
        -- exact C3.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m4) (le1:=le).
        -- eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero;Vint (Int.repr 7)]) (v:=Vundef).
           ++ curve_symbol.
           ++ reflexivity.
           ++ curve_arguments HA.
           ++ exact C4.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m5) (le1:=le).
           ++ eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero]) (v:=Vundef).
              ** curve_symbol.
              ** reflexivity.
              ** curve_arguments HA.
              ** exact C5.
           ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint v) le).
              ** eapply exec_curve_call with (vargs:=[Vptr b_y2 Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vint v).
                 --- curve_symbol.
                 --- reflexivity.
                 --- curve_arguments HA.
                 --- exact C6.
              ** apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
Qed.
