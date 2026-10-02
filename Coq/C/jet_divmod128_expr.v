(** The actual short-circuit normalized-divisor/quotient-bound guard of the
    public DivMod128_64 C jet, and its exact machine preconditions. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_divmod128_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod128_normal_expr :=
  Ebinop Ole (Econst_long (Int64.repr (-9223372036854775808)) tulong) (Etempvar _b tulong) tint.
Definition divmod128_bound_expr := Ebinop Olt (Etempvar _ah tulong) (Etempvar _b tulong) tint.
Definition divmod128_guard_stmt :=
  Sifthenelse divmod128_normal_expr
    (Sset _t'5 (Ecast divmod128_bound_expr tbool))
    (Sset _t'5 (Econst_int Int.zero tint)).

Lemma eval_divmod128_normal_expr e le m b : le!_b = Some (Vlong b) ->
  eval_expr ge0 e le m divmod128_normal_expr
    (Vint (bit_int (negb (Int64.ltu b (Int64.repr 9223372036854775808))))).
Proof.
  intros HB. eapply eval_Ebinop with (v1 := Vlong (Int64.repr (-9223372036854775808))) (v2 := Vlong b).
  - apply eval_Econst_long.
  - apply eval_Etempvar; exact HB.
  - change (Some (Val.of_bool (negb (Int64.ltu b (Int64.repr 9223372036854775808)))) =
      Some (Vint (bit_int (negb (Int64.ltu b (Int64.repr 9223372036854775808)))))).
    destruct (Int64.ltu b (Int64.repr 9223372036854775808)); reflexivity.
Qed.

Lemma eval_divmod128_bound_expr e le m ah b : le!_ah = Some (Vlong ah) -> le!_b = Some (Vlong b) ->
  eval_expr ge0 e le m divmod128_bound_expr (Vint (bit_int (Int64.ltu ah b))).
Proof.
  intros HA HB. eapply eval_Ebinop with (v1 := Vlong ah) (v2 := Vlong b).
  - apply eval_Etempvar; exact HA.
  - apply eval_Etempvar; exact HB.
  - change (Some (Val.of_bool (Int64.ltu ah b)) = Some (Vint (bit_int (Int64.ltu ah b)))).
    destruct (Int64.ltu ah b); reflexivity.
Qed.

Lemma exec_divmod128_guard_stmt e le m ah b : le!_ah = Some (Vlong ah) -> le!_b = Some (Vlong b) ->
  Clight2.exec_stmt ge0 e le m divmod128_guard_stmt E0
    (PTree.set _t'5 (Vint (bit_int (divmod128_guard ah b))) le) m Out_normal.
Proof.
  intros HA HB. pose proof (eval_divmod128_normal_expr e le m b HB) as HC.
  unfold divmod128_guard.
  destruct (Int64.ltu b (Int64.repr 9223372036854775808)) eqn:HG; cbn [negb andb].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. apply eval_Econst_int.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int (Int64.ltu ah b))).
      * apply eval_divmod128_bound_expr; assumption.
      * destruct (Int64.ltu ah b); reflexivity.
Qed.

Lemma divmod128_guard_preconditions ah b : divmod128_guard ah b = Datatypes.true <->
  Int64.modulus <= 2 * Int64.unsigned b /\ Int64.unsigned ah < Int64.unsigned b.
Proof.
  unfold divmod128_guard, Int64.ltu.
  change (Int64.unsigned (Int64.repr 9223372036854775808)) with 9223372036854775808.
  change Int64.modulus with 18446744073709551616.
  destruct (zlt (Int64.unsigned b) 9223372036854775808),
    (zlt (Int64.unsigned ah) (Int64.unsigned b)); cbn [negb andb];
    split; intros; try discriminate; try reflexivity; lia.
Qed.
