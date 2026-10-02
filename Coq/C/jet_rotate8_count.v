(** Actual byte rotation count arithmetic, including signed C remainder and
    uchar casts. This adapter covers width 8, which is not a wide_size. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_rotate_count_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate8_amount a := Int.repr (Int.unsigned a mod 8).
Definition rotate8_amount_expr input := Ecast
  (Ebinop Omod input (Econst_int (Int.repr 8) tint) tint) tuchar.

Lemma rotate8_amount_unsigned a :
  Int.unsigned (rotate8_amount a) = Int.unsigned a mod 8.
Proof.
  pose proof (Z.mod_pos_bound (Int.unsigned a) 8 ltac:(lia)) as HM.
  unfold rotate8_amount. apply Int.unsigned_repr.
  change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma rotate8_amount_bounds a :
  0 <= Int.unsigned (rotate8_amount a) < 8.
Proof. rewrite rotate8_amount_unsigned; apply Z.mod_pos_bound; lia. Qed.

Lemma rotate8_amount_cast_id a : Int.zero_ext 8 (rotate8_amount a) = rotate8_amount a.
Proof. apply byte_carrier_cast_id. pose proof (rotate8_amount_bounds a); lia. Qed.

Lemma eval_rotate8_amount e le m input a :
  (typeof input = tuchar \/ typeof input = tint) -> eval_expr ge0 e le m input (Vint a) ->
  0 <= Int.unsigned a < 256 ->
  eval_expr ge0 e le m (rotate8_amount_expr input) (Vint (rotate8_amount a)).
Proof.
  intros HT HE HA.
  assert (HD0 : Int.eq (Int.repr 8) Int.zero = Datatypes.false) by (reflexivity).
  assert (HDm : Int.eq (Int.repr 8) Int.mone = Datatypes.false) by (reflexivity).
  assert (Hs : Int.signed a = Int.unsigned a).
  { apply Int.signed_eq_unsigned. change Int.max_signed with 2147483647; lia. }
  assert (HS : Int.signed (Int.repr 8) = 8).
  { apply Int.signed_repr. change Int.min_signed with (-2147483648).
    change Int.max_signed with 2147483647; lia. }
  unfold rotate8_amount_expr.
  eapply eval_Ecast with (v1 := Vint (rotate8_amount a)).
  - eapply eval_Ebinop with (v1 := Vint a) (v2 := Vint (Int.repr 8)).
    + exact HE.
    + constructor.
    + destruct HT as [HT|HT]; rewrite HT.
      all: change ((if Int.eq (Int.repr 8) Int.zero ||
        Int.eq a (Int.repr Int.min_signed) && Int.eq (Int.repr 8) Int.mone
        then None else Some (Vint (Int.mods a (Int.repr 8)))) =
        Some (Vint (rotate8_amount a))).
      all: rewrite HD0, HDm, andb_false_r; cbn [orb].
      all: unfold Int.mods, rotate8_amount; rewrite Hs, HS, Z.rem_mod_nonneg by lia; reflexivity.
  - change (Some (Vint (Int.zero_ext 8 (rotate8_amount a))) = Some (Vint (rotate8_amount a))).
    rewrite rotate8_amount_cast_id; reflexivity.
Qed.

Definition rotate8_reverse_amount a :=
  rotate8_amount (Int.repr (8 - Int.unsigned a)).
Definition rotate8_reverse_amount_expr := rotate8_amount_expr
  (Ebinop Osub (Econst_int (Int.repr 8) tint) (Etempvar _amt tuchar) tint).

Lemma rotate8_reverse_amount_unsigned a :
  0 <= Int.unsigned a < 8 ->
  Int.unsigned (rotate8_reverse_amount a) = (8 - Int.unsigned a) mod 8.
Proof.
  intros HA.
  unfold rotate8_reverse_amount. rewrite rotate8_amount_unsigned, Int.unsigned_repr;
    [reflexivity|change Int.max_unsigned with 4294967295; lia].
Qed.

Lemma eval_rotate8_reverse_amount e le m a :
  0 <= Int.unsigned a < 8 -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (rotate8_reverse_amount_expr) (Vint (rotate8_reverse_amount a)).
Proof.
  intros HA HL.
  assert (HRange : 0 <= 8 - Int.unsigned a <= Int.max_unsigned).
  { change Int.max_unsigned with 4294967295; lia. }
  unfold rotate8_reverse_amount_expr, rotate8_reverse_amount.
  apply eval_rotate8_amount.
  - right; reflexivity.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 8)) (v2 := Vint a).
    + constructor.
    + apply eval_Etempvar; exact HL.
    + change (Some (Vint (Int.sub (Int.repr 8) a)) =
        Some (Vint (Int.repr (8 - Int.unsigned a)))).
      unfold Int.sub. rewrite Int.unsigned_repr; [reflexivity|].
      change Int.max_unsigned with 4294967295; lia.
  - rewrite Int.unsigned_repr by exact HRange; lia.
Qed.
