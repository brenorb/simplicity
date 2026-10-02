(** Actual guarded remainder and zero-test statements for C divides jets. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_division_value C.jet_division8_expr.
Require Import C.jet_divides_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divides8_choose :=
  Sifthenelse (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _x tuchar) tint)
    (Sset _t'3 (Ecast (Etempvar _y tuchar) tint))
    (Sset _t'3 (Ecast (Ebinop Omod (Etempvar _y tuchar) (Etempvar _x tuchar) tint) tint)).
Definition divides8_test_expr := Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _t'3 tint) tint.
Definition wide_divides_choose :=
  Sifthenelse (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _x tulong) tint)
    (Sset _t'3 (Ecast (Etempvar _y tulong) tulong))
    (Sset _t'3 (Ecast (Ebinop Omod (Etempvar _y tulong) (Etempvar _x tulong) tulong) tulong)).
Definition wide_divides_test_expr := Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _t'3 tulong) tint.

Lemma exec_divides8_choose e le m r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  Clight2.exec_stmt ge0 e le m divides8_choose E0
    (PTree.set _t'3 (Vint (division8_raw Datatypes.true t r)) le) m Out_normal.
Proof.
  intros HX HY.
  assert (HC : eval_expr ge0 e le m
    (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _x tuchar) tint)
    (Vint (bit_int (Int.eq Int.zero (Int.zero_ext 8 r))))).
  { eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint (Int.zero_ext 8 r)).
    - apply eval_Econst_int.
    - apply eval_Etempvar; exact HX.
    - change (Some (Val.of_bool (Int.eq Int.zero (Int.zero_ext 8 r))) =
        Some (Vint (bit_int (Int.eq Int.zero (Int.zero_ext 8 r))))).
      destruct (Int.eq Int.zero (Int.zero_ext 8 r)); reflexivity. }
  destruct (Int.eq Int.zero (Int.zero_ext 8 r)) eqn:HZ; unfold division8_raw; rewrite HZ.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; exact HY|reflexivity].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vint (division8_nonzero Datatypes.true t r)); [|reflexivity].
      eapply eval_Ebinop with (v1 := Vint (Int.zero_ext 8 t)) (v2 := Vint (Int.zero_ext 8 r)).
      * apply eval_Etempvar; exact HY.
      * apply eval_Etempvar; exact HX.
      * change ((if Int.eq (Int.zero_ext 8 r) Int.zero ||
          Int.eq (Int.zero_ext 8 t) (Int.repr Int.min_signed) && Int.eq (Int.zero_ext 8 r) Int.mone
          then None else Some (Vint (Int.mods (Int.zero_ext 8 t) (Int.zero_ext 8 r)))) =
          Some (Vint (Int.mods (Int.zero_ext 8 t) (Int.zero_ext 8 r)))).
        rewrite (Int.eq_sym _ Int.zero), HZ, division8_not_mone, Bool.andb_false_r. reflexivity.
Qed.

Lemma eval_divides8_test_expr e le m r t :
  le!_t'3 = Some (Vint (division8_raw Datatypes.true t r)) ->
  eval_expr ge0 e le m divides8_test_expr (Vint (bit_int (divides8_bit r t))).
Proof.
  intros HT. eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint (division8_raw Datatypes.true t r)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HT.
  - change (Some (Val.of_bool (divides8_bit r t)) = Some (Vint (bit_int (divides8_bit r t)))).
    destruct (divides8_bit r t); reflexivity.
Qed.

Lemma exec_wide_divides_choose e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  Clight2.exec_stmt ge0 e le m wide_divides_choose E0
    (PTree.set _t'3 (Vlong (division_wide_raw Datatypes.true t r)) le) m Out_normal.
Proof.
  intros HX HY.
  assert (HC : eval_expr ge0 e le m
    (Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _x tulong) tint)
    (Vint (bit_int (Int64.eq Int64.zero r)))).
  { eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong r).
    - apply eval_Econst_int.
    - apply eval_Etempvar; exact HX.
    - change (Some (Val.of_bool (Int64.eq Int64.zero r)) = Some (Vint (bit_int (Int64.eq Int64.zero r)))).
      destruct (Int64.eq Int64.zero r); reflexivity. }
  destruct (Int64.eq Int64.zero r) eqn:HZ; unfold division_wide_raw; rewrite HZ.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; exact HY|reflexivity].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vlong (Int64.modu t r)); [|reflexivity].
      eapply eval_Ebinop with (v1 := Vlong t) (v2 := Vlong r).
      * apply eval_Etempvar; exact HY.
      * apply eval_Etempvar; exact HX.
      * change ((if Int64.eq r Int64.zero then None else Some (Vlong (Int64.modu t r))) =
          Some (Vlong (Int64.modu t r))). rewrite Int64.eq_sym, HZ. reflexivity.
Qed.

Lemma eval_wide_divides_test_expr e le m r t :
  le!_t'3 = Some (Vlong (division_wide_raw Datatypes.true t r)) ->
  eval_expr ge0 e le m wide_divides_test_expr (Vint (bit_int (wide_divides_bit r t))).
Proof.
  intros HT. eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong (division_wide_raw Datatypes.true t r)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HT.
  - change (Some (Val.of_bool (wide_divides_bit r t)) = Some (Vint (bit_int (wide_divides_bit r t)))).
    destruct (wide_divides_bit r t); reflexivity.
Qed.
