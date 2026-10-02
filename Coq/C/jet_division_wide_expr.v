(** Actual LP64 unsigned long division/remainder expressions at all wide
    logical widths. Zero is handled by the C branch before evaluating them. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_division_value C.jet_division8_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition division_wide_nonzero (remainder : bool) r t :=
  if remainder then Int64.modu r t else Int64.divu r t.
Definition division_wide_expr remainder :=
  Ebinop (division_binop remainder) (Etempvar _x tulong) (Etempvar _y tulong) tulong.
Definition division_wide_zero_expr := Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _y tulong) tint.
Definition division_wide_choose (remainder : bool) :=
  Sifthenelse division_wide_zero_expr
    (Sset _t'3 (Ecast (if remainder then Etempvar _x tulong else Econst_int Int.zero tint) tulong))
    (Sset _t'3 (Ecast (division_wide_expr remainder) tulong)).

Lemma eval_division_wide_zero_expr e le m t : le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m division_wide_zero_expr
    (Vint (bit_int (Int64.eq Int64.zero t))).
Proof.
  intros HY. eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong t).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HY.
  - change (Some (Val.of_bool (Int64.eq Int64.zero t)) =
      Some (Vint (bit_int (Int64.eq Int64.zero t)))).
    destruct (Int64.eq Int64.zero t); reflexivity.
Qed.

Lemma eval_division_wide_nonzero_expr remainder e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  Int64.eq Int64.zero t = Datatypes.false ->
  eval_expr ge0 e le m (division_wide_expr remainder) (Vlong (division_wide_nonzero remainder r t)).
Proof.
  intros HX HY HNZ. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - apply eval_Etempvar; exact HX.
  - apply eval_Etempvar; exact HY.
  - destruct remainder.
    + change ((if Int64.eq t Int64.zero then None else Some (Vlong (Int64.modu r t))) =
        Some (Vlong (Int64.modu r t))).
      rewrite Int64.eq_sym, HNZ; reflexivity.
    + change ((if Int64.eq t Int64.zero then None else Some (Vlong (Int64.divu r t))) =
        Some (Vlong (Int64.divu r t))).
      rewrite Int64.eq_sym, HNZ; reflexivity.
Qed.

Lemma exec_division_wide_choose remainder e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  Clight2.exec_stmt ge0 e le m (division_wide_choose remainder)
    E0 (PTree.set _t'3 (Vlong (division_wide_raw remainder r t)) le) m Out_normal.
Proof.
  intros HX HY. pose proof (eval_division_wide_zero_expr e le m t HY) as HC.
  destruct (Int64.eq Int64.zero t) eqn:HZ; unfold division_wide_raw; rewrite HZ.
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
      * exact (eval_division_wide_nonzero_expr remainder e le m r t HX HY HZ).
      * destruct remainder; reflexivity.
Qed.
