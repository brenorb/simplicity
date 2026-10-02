(** Guarded scalar arithmetic with an explicit destination temporary.
    div_mod uses _t'3 for quotient and _t'4 for remainder. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_division_value.
Require Import C.jet_division8_expr C.jet_division_wide_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod8_choose target (remainder : bool) :=
  Sifthenelse division8_zero_expr
    (Sset target (Ecast (if remainder then Etempvar _x tuchar else Econst_int Int.zero tint) tint))
    (Sset target (Ecast (division8_expr remainder) tint)).

Lemma exec_divmod8_choose target remainder e le m r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  Clight2.exec_stmt ge0 e le m (divmod8_choose target remainder)
    E0 (PTree.set target (Vint (division8_raw remainder r t)) le) m Out_normal.
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

Definition divmod_wide_choose target (remainder : bool) :=
  Sifthenelse division_wide_zero_expr
    (Sset target (Ecast (if remainder then Etempvar _x tulong else Econst_int Int.zero tint) tulong))
    (Sset target (Ecast (division_wide_expr remainder) tulong)).

Lemma exec_divmod_wide_choose target remainder e le m r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  Clight2.exec_stmt ge0 e le m (divmod_wide_choose target remainder)
    E0 (PTree.set target (Vlong (division_wide_raw remainder r t)) le) m Out_normal.
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
