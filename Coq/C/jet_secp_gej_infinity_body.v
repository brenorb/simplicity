(** Actual unchanged point initializer: entry and composition of original calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events ClightBigstep Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jet_secp_fns C.jets_secp.
Require Import C.jet_secp_gej_infinity_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_infinity_clear_stmt fid : statement :=
  Scall None
    (Evar _secp256k1_fe_clear (Tfunction
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil) tvoid cc_default))
    [Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
       (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr))
       (tptr (Tstruct __5467 noattr))].
Definition gej_infinity_flag_stmt : statement :=
  Sassign (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) _infinity tint) (Econst_int (Int.repr 1) tint).
Lemma gej_infinity_initializer_body : fn_body f_secp256k1_gej_set_infinity =
  Ssequence gej_infinity_flag_stmt
    (Ssequence (gej_infinity_clear_stmt _x)
      (Ssequence (gej_infinity_clear_stmt _y) (gej_infinity_clear_stmt _z))).
Proof. reflexivity. Qed.

Lemma exec_gej_infinity_clear_call le m mf b base fid delta :
  In (fid, delta) [(_x,0); (_y,40); (_z,80)] ->
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr (base + delta))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (gej_infinity_clear_stmt fid)
    E0 le mf Out_normal.
Proof.
  intros HF HB HM HR HCall.
  destruct (secp_pure_ok _secp256k1_fe_clear f_secp256k1_fe_clear
    ltac:(unfold secp_pure; repeat (first [left; reflexivity|right])))
    as [bf [HS HFunc]].
  unfold gej_infinity_clear_stmt.
  eapply ClightBigstep.exec_Scall with (vf := Vptr bf Ptrofs.zero)
    (vargs := [Vptr b (Ptrofs.repr (base + delta))])
    (f := Internal f_secp256k1_fe_clear) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + exact (eval_gej_infinity_field_address le m b base fid delta HF HB HM HR).
    + reflexivity.
    + apply eval_Enil.
  - change (Genv.find_funct_ptr secp_ge bf = Some (Internal f_secp256k1_fe_clear)).
    exact HFunc.
  - reflexivity.
  - exact HCall.
Qed.

Definition gej_infinity_env b base :=
  PTree.set _r (Vptr b (Ptrofs.repr base))
    (create_undef_temps (fn_temps f_secp256k1_gej_set_infinity)).
Lemma gej_infinity_initializer_entry m b base :
  function_entry2 secp_ge f_secp256k1_gej_set_infinity [Vptr b (Ptrofs.repr base)]
    m empty_env (gej_infinity_env b base) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros x y HX HY HE. cbn in HX, HY. contradiction.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_gej_infinity_initializer_from_calls m mi mx my mf b base :
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  Clight2.exec_stmt secp_ge empty_env (gej_infinity_env b base) m
    gej_infinity_flag_stmt E0 (gej_infinity_env b base) mi Out_normal ->
  Clight2.eval_funcall secp_ge mi (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr (base + 0))] E0 mx Vundef ->
  Clight2.eval_funcall secp_ge mx (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr (base + 40))] E0 my Vundef ->
  Clight2.eval_funcall secp_ge my (Internal f_secp256k1_fe_clear)
    [Vptr b (Ptrofs.repr (base + 80))] E0 mf Vundef ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_infinity)
    [Vptr b (Ptrofs.repr base)] E0 mf Vundef.
Proof.
  intros HB HM HFlag HX HY HZ.
  assert (HR : (gej_infinity_env b base)!_r = Some (Vptr b (Ptrofs.repr base))).
  { unfold gej_infinity_env; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := gej_infinity_env b base) (le2 := gej_infinity_env b base)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply gej_infinity_initializer_entry.
  - rewrite gej_infinity_initializer_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi)
      (le1 := gej_infinity_env b base); [exact HFlag|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx)
      (le1 := gej_infinity_env b base).
    + eapply exec_gej_infinity_clear_call; [left;reflexivity|exact HB|exact HM|exact HR|exact HX].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := my)
        (le1 := gej_infinity_env b base).
      * eapply exec_gej_infinity_clear_call; [right;left;reflexivity|exact HB|exact HM|exact HR|exact HY].
      * eapply exec_gej_infinity_clear_call; [right;right;left;reflexivity|exact HB|exact HM|exact HR|exact HZ].
  - reflexivity.
  - reflexivity.
Qed.
Print Assumptions eval_gej_infinity_initializer_from_calls.
