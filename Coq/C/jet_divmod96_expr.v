(** Actual scalar expression trees in the div_mod_96_64 Clight helper.
    The full memory-aware function/loop execution remains a separate task. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_divmod96_value.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_first_guard_expr :=
  Ebinop Ole (Etempvar _rh tulong) (Econst_int Int.mone tuint) tint.
Definition divmod96_sum_expr :=
  Ebinop Oadd
    (Ebinop Omul (Econst_long (Int64.repr divmod96_radix) tulong) (Etempvar _rh tulong) tulong)
    (Etempvar _al tulong) tulong.
Definition divmod96_second_guard_expr := Ebinop Olt divmod96_sum_expr (Etempvar _d tulong) tint.
Definition divmod96_guard_stmt :=
  Sifthenelse divmod96_first_guard_expr
    (Sset _t'2 (Ecast divmod96_second_guard_expr tbool))
    (Sset _t'2 (Econst_int Int.zero tint)).
Definition divmod96_final_expr := Ebinop Osub divmod96_sum_expr (Etempvar _d tulong) tulong.

Lemma eval_divmod96_high_expr e le m b : le!_b = Some (Vlong b) ->
  eval_expr ge0 e le m
    (Ebinop Oshr (Etempvar _b tulong) (Econst_int (Int.repr 32) tint) tulong)
    (Vlong (divmod96_high b)).
Proof.
  intros HB. eapply eval_Ebinop with (v1 := Vlong b) (v2 := Vint (Int.repr 32)).
  - apply eval_Etempvar; exact HB.
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Lemma eval_divmod96_low_expr e le m b : le!_b = Some (Vlong b) ->
  eval_expr ge0 e le m
    (Ebinop Oand (Etempvar _b tulong) (Econst_int Int.mone tuint) tulong)
    (Vlong (divmod96_low b)).
Proof.
  intros HB. eapply eval_Ebinop with (v1 := Vlong b) (v2 := Vint Int.mone).
  - apply eval_Etempvar; exact HB.
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Lemma eval_divmod96_sum_expr e le m rh al :
  le!_rh = Some (Vlong rh) -> le!_al = Some (Vlong al) ->
  eval_expr ge0 e le m divmod96_sum_expr
    (Vlong (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al)).
Proof.
  intros HR HA. eapply eval_Ebinop with
    (v1 := Vlong (Int64.mul (Int64.repr divmod96_radix) rh)) (v2 := Vlong al).
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr divmod96_radix)) (v2 := Vlong rh).
    + apply eval_Econst_long.
    + apply eval_Etempvar; exact HR.
    + reflexivity.
  - apply eval_Etempvar; exact HA.
  - reflexivity.
Qed.

Lemma eval_divmod96_first_guard_expr e le m rh : le!_rh = Some (Vlong rh) ->
  eval_expr ge0 e le m divmod96_first_guard_expr
    (Vint (bit_int (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh)))).
Proof.
  intros HR. eapply eval_Ebinop with (v1 := Vlong rh) (v2 := Vint Int.mone).
  - apply eval_Etempvar; exact HR.
  - apply eval_Econst_int.
  - change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh))) =
      Some (Vint (bit_int (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh))))).
    destruct (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh); reflexivity.
Qed.

Lemma eval_divmod96_second_guard_expr e le m rh al d :
  le!_rh = Some (Vlong rh) -> le!_al = Some (Vlong al) -> le!_d = Some (Vlong d) ->
  eval_expr ge0 e le m divmod96_second_guard_expr
    (Vint (bit_int (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d))).
Proof.
  intros HR HA HD. eapply eval_Ebinop with
    (v1 := Vlong (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al)) (v2 := Vlong d).
  - apply eval_divmod96_sum_expr; assumption.
  - apply eval_Etempvar; exact HD.
  - change (Some (Val.of_bool (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d)) =
      Some (Vint (bit_int (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d)))).
    destruct (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d); reflexivity.
Qed.

Lemma exec_divmod96_guard_stmt e le m rh al d :
  le!_rh = Some (Vlong rh) -> le!_al = Some (Vlong al) -> le!_d = Some (Vlong d) ->
  Clight2.exec_stmt ge0 e le m divmod96_guard_stmt
    E0 (PTree.set _t'2 (Vint (bit_int (divmod96_guard rh al d))) le) m Out_normal.
Proof.
  intros HR HA HD. pose proof (eval_divmod96_first_guard_expr e le m rh HR) as HC.
  unfold divmod96_guard.
  destruct (Int64.ltu (Int64.repr (divmod96_radix - 1)) rh) eqn:HG; cbn [negb].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. apply eval_Econst_int.
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with
        (v1 := Vint (bit_int (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d))).
      * apply eval_divmod96_second_guard_expr; assumption.
      * destruct (Int64.ltu (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al) d); reflexivity.
Qed.

Lemma eval_divmod96_final_expr e le m rh al d :
  le!_rh = Some (Vlong rh) -> le!_al = Some (Vlong al) -> le!_d = Some (Vlong d) ->
  eval_expr ge0 e le m divmod96_final_expr
    (Vlong (Int64.repr (divmod96_radix * Int64.unsigned rh + Int64.unsigned al - Int64.unsigned d))).
Proof.
  intros HR HA HD. rewrite <- divmod96_final_modular.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.add (Int64.mul (Int64.repr divmod96_radix) rh) al)) (v2 := Vlong d).
  - apply eval_divmod96_sum_expr; assumption.
  - apply eval_Etempvar; exact HD.
  - reflexivity.
Qed.
