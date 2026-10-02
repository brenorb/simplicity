(** Exact promoted signed remainder and uchar conversions used by rotations.
    The reader supplies a byte carrier; the divisor is always positive. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_wide.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_rotate_amount s a := Int.repr (Int.unsigned a mod wide_bits s).
Definition wide_rotate_amount_expr s input := Ecast
  (Ebinop Omod input (Econst_int (Int.repr (wide_bits s)) tint) tint) tuchar.

Lemma byte_carrier_cast_id a :
  0 <= Int.unsigned a < 256 -> Int.zero_ext 8 a = a.
Proof.
  intros HA. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 a)).
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (Int.repr (Int.unsigned a mod 256) = a).
  rewrite Z.mod_small by exact HA. apply Int.repr_unsigned.
Qed.

Lemma wide_rotate_amount_unsigned s a :
  Int.unsigned (wide_rotate_amount s a) = Int.unsigned a mod wide_bits s.
Proof.
  pose proof (wide_bits_bounds s) as HW.
  pose proof (Z.mod_pos_bound (Int.unsigned a) (wide_bits s) ltac:(lia)) as HM.
  unfold wide_rotate_amount. apply Int.unsigned_repr.
  change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma wide_rotate_amount_bounds s a :
  0 <= Int.unsigned (wide_rotate_amount s a) < wide_bits s.
Proof. rewrite wide_rotate_amount_unsigned; apply Z.mod_pos_bound; pose proof (wide_bits_bounds s); lia. Qed.

Lemma wide_rotate_amount_cast_id s a : Int.zero_ext 8 (wide_rotate_amount s a) = wide_rotate_amount s a.
Proof. apply byte_carrier_cast_id. pose proof (wide_rotate_amount_bounds s a); pose proof (wide_bits_bounds s); lia. Qed.

Lemma eval_wide_rotate_amount s e le m input a :
  (typeof input = tuchar \/ typeof input = tint) -> eval_expr ge0 e le m input (Vint a) ->
  0 <= Int.unsigned a < 256 ->
  eval_expr ge0 e le m (wide_rotate_amount_expr s input) (Vint (wide_rotate_amount s a)).
Proof.
  intros HT HE HA. pose proof (wide_bits_bounds s) as HW.
  assert (HD0 : Int.eq (Int.repr (wide_bits s)) Int.zero = Datatypes.false) by (destruct s; reflexivity).
  assert (HDm : Int.eq (Int.repr (wide_bits s)) Int.mone = Datatypes.false) by (destruct s; reflexivity).
  assert (Hs : Int.signed a = Int.unsigned a).
  { apply Int.signed_eq_unsigned. change Int.max_signed with 2147483647; lia. }
  assert (HS : Int.signed (Int.repr (wide_bits s)) = wide_bits s).
  { apply Int.signed_repr. change Int.min_signed with (-2147483648).
    change Int.max_signed with 2147483647; lia. }
  unfold wide_rotate_amount_expr.
  eapply eval_Ecast with (v1 := Vint (wide_rotate_amount s a)).
  - eapply eval_Ebinop with (v1 := Vint a) (v2 := Vint (Int.repr (wide_bits s))).
    + exact HE.
    + constructor.
    + destruct HT as [HT|HT]; rewrite HT.
      all: change ((if Int.eq (Int.repr (wide_bits s)) Int.zero ||
        Int.eq a (Int.repr Int.min_signed) && Int.eq (Int.repr (wide_bits s)) Int.mone
        then None else Some (Vint (Int.mods a (Int.repr (wide_bits s))))) =
        Some (Vint (wide_rotate_amount s a))).
      all: rewrite HD0, HDm, andb_false_r; cbn [orb].
      all: unfold Int.mods, wide_rotate_amount; rewrite Hs, HS, Z.rem_mod_nonneg by lia; reflexivity.
  - change (Some (Vint (Int.zero_ext 8 (wide_rotate_amount s a))) = Some (Vint (wide_rotate_amount s a))).
    rewrite wide_rotate_amount_cast_id; reflexivity.
Qed.

Definition wide_rotate_reverse_amount s a :=
  wide_rotate_amount s (Int.repr (wide_bits s - Int.unsigned a)).
Definition wide_rotate_reverse_amount_expr s := wide_rotate_amount_expr s
  (Ebinop Osub (Econst_int (Int.repr (wide_bits s)) tint) (Etempvar _amt tuchar) tint).

Lemma wide_rotate_reverse_amount_unsigned s a :
  0 <= Int.unsigned a < wide_bits s ->
  Int.unsigned (wide_rotate_reverse_amount s a) = (wide_bits s - Int.unsigned a) mod wide_bits s.
Proof.
  intros HA. pose proof (wide_bits_bounds s) as HW.
  unfold wide_rotate_reverse_amount. rewrite wide_rotate_amount_unsigned, Int.unsigned_repr;
    [reflexivity|change Int.max_unsigned with 4294967295; lia].
Qed.

Lemma eval_wide_rotate_reverse_amount s e le m a :
  0 <= Int.unsigned a < wide_bits s -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (wide_rotate_reverse_amount_expr s) (Vint (wide_rotate_reverse_amount s a)).
Proof.
  intros HA HL. pose proof (wide_bits_bounds s) as HW.
  assert (HRange : 0 <= wide_bits s - Int.unsigned a <= Int.max_unsigned).
  { change Int.max_unsigned with 4294967295; lia. }
  unfold wide_rotate_reverse_amount_expr, wide_rotate_reverse_amount.
  apply eval_wide_rotate_amount.
  - right; reflexivity.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr (wide_bits s))) (v2 := Vint a).
    + constructor.
    + apply eval_Etempvar; exact HL.
    + change (Some (Vint (Int.sub (Int.repr (wide_bits s)) a)) =
        Some (Vint (Int.repr (wide_bits s - Int.unsigned a)))).
      unfold Int.sub. rewrite Int.unsigned_repr; [reflexivity|].
      change Int.max_unsigned with 4294967295; lia.
  - rewrite Int.unsigned_repr by exact HRange; lia.
Qed.
