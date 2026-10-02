(** Actual promoted signed byte division/remainder, guarded against zero.
    This executes C scalar expressions; no canonical jet coverage is claimed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_division_value C.jet_add8_word C.jet_add8.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition division_binop (remainder : bool) := if remainder then Omod else Odiv.
Definition division8_expr remainder :=
  Ebinop (division_binop remainder) (Etempvar _x tuchar) (Etempvar _y tuchar) tint.
Definition division8_zero_expr := Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _y tuchar) tint.
Definition division8_choose (remainder : bool) :=
  Sifthenelse division8_zero_expr
    (Sset _t'3 (Ecast (if remainder then Etempvar _x tuchar else Econst_int Int.zero tint) tint))
    (Sset _t'3 (Ecast (division8_expr remainder) tint)).

Lemma division8_not_mone t : Int.eq (Int.zero_ext 8 t) Int.mone = Datatypes.false.
Proof.
  apply Int.eq_false. intro H.
  pose proof (add8_u_range t) as HT. unfold add8_u in HT.
  apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_mone in H.
  change Int.modulus with 4294967296 in H; lia.
Qed.

Lemma eval_division8_zero_expr e le m t : le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  eval_expr ge0 e le m division8_zero_expr
    (Vint (bit_int (Int.eq Int.zero (Int.zero_ext 8 t)))).
Proof.
  intros HY. eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vint (Int.zero_ext 8 t)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HY.
  - change (Some (Val.of_bool (Int.eq Int.zero (Int.zero_ext 8 t))) =
      Some (Vint (bit_int (Int.eq Int.zero (Int.zero_ext 8 t))))).
    destruct (Int.eq Int.zero (Int.zero_ext 8 t)); reflexivity.
Qed.

Lemma eval_division8_nonzero_expr remainder e le m r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  Int.eq Int.zero (Int.zero_ext 8 t) = Datatypes.false ->
  eval_expr ge0 e le m (division8_expr remainder) (Vint (division8_nonzero remainder r t)).
Proof.
  intros HX HY HNZ. eapply eval_Ebinop with
    (v1 := Vint (Int.zero_ext 8 r)) (v2 := Vint (Int.zero_ext 8 t)).
  - apply eval_Etempvar; exact HX.
  - apply eval_Etempvar; exact HY.
  - destruct remainder.
    + change ((if Int.eq (Int.zero_ext 8 t) Int.zero ||
        Int.eq (Int.zero_ext 8 r) (Int.repr Int.min_signed) && Int.eq (Int.zero_ext 8 t) Int.mone
        then None else Some (Vint (Int.mods (Int.zero_ext 8 r) (Int.zero_ext 8 t)))) =
        Some (Vint (Int.mods (Int.zero_ext 8 r) (Int.zero_ext 8 t)))).
      rewrite (Int.eq_sym _ Int.zero), HNZ, division8_not_mone, Bool.andb_false_r; reflexivity.
    + change ((if Int.eq (Int.zero_ext 8 t) Int.zero ||
        Int.eq (Int.zero_ext 8 r) (Int.repr Int.min_signed) && Int.eq (Int.zero_ext 8 t) Int.mone
        then None else Some (Vint (Int.divs (Int.zero_ext 8 r) (Int.zero_ext 8 t)))) =
        Some (Vint (Int.divs (Int.zero_ext 8 r) (Int.zero_ext 8 t)))).
      rewrite (Int.eq_sym _ Int.zero), HNZ, division8_not_mone, Bool.andb_false_r; reflexivity.
Qed.

Lemma exec_division8_choose remainder e le m r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  Clight2.exec_stmt ge0 e le m (division8_choose remainder)
    E0 (PTree.set _t'3 (Vint (division8_raw remainder r t)) le) m Out_normal.
Proof.
  intros HX HY. pose proof (eval_division8_zero_expr e le m t HY) as HC.
  destruct (Int.eq Int.zero (Int.zero_ext 8 t)) eqn:HZ; unfold division8_raw; rewrite HZ.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + destruct remainder; apply exec_set; eapply eval_Ecast.
      * apply eval_Etempvar; exact HX.
      * reflexivity.
      * apply eval_Econst_int.
      * reflexivity.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast.
      * exact (eval_division8_nonzero_expr remainder e le m r t HX HY HZ).
      * reflexivity.
Qed.
