(** Internal C division values. These numeric facts are not canonical jet
    specifications and do not by themselves establish any jet coverage. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_add8 C.jet_add8_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition division_numeric (remainder : bool) a b :=
  if Z.eqb b 0 then (if remainder then a else 0)
  else if remainder then a mod b else a / b.
Definition division8_nonzero (remainder : bool) r t :=
  if remainder then Int.mods (Int.zero_ext 8 r) (Int.zero_ext 8 t)
  else Int.divs (Int.zero_ext 8 r) (Int.zero_ext 8 t).
Definition division8_raw (remainder : bool) r t :=
  if Int.eq Int.zero (Int.zero_ext 8 t) then
    (if remainder then Int.zero_ext 8 r else Int.zero)
  else division8_nonzero remainder r t.
Definition division8_payload remainder r t := Int.zero_ext 8 (division8_raw remainder r t).
Definition division_wide_raw (remainder : bool) r t :=
  if Int64.eq Int64.zero t then (if remainder then r else Int64.zero)
  else if remainder then Int64.modu r t else Int64.divu r t.

Lemma division_numeric_range remainder a b bound :
  0 <= a < bound -> 0 <= b < bound ->
  0 <= division_numeric remainder a b < bound.
Proof.
  intros HA HB. unfold division_numeric. destruct (Z.eqb_spec b 0) as [HZ|HN].
  - destruct remainder; lia.
  - assert (HP : 0 < b) by lia. destruct remainder.
    + pose proof (Z.mod_pos_bound a b HP); lia.
    + split; [apply Z.div_pos; lia|].
      assert (a / b <= a) by (apply Z.div_le_upper_bound; nia). lia.
Qed.

Lemma division8_zero_test t :
  Int.eq Int.zero (Int.zero_ext 8 t) = Z.eqb (Int.unsigned (Int.zero_ext 8 t)) 0.
Proof.
  unfold Int.eq. rewrite Int.unsigned_zero. destruct (zeq 0 (Int.unsigned (Int.zero_ext 8 t)));
    symmetry; [apply Z.eqb_eq|apply Z.eqb_neq]; lia.
Qed.

Lemma division8_signed r : Int.signed (Int.zero_ext 8 r) = Int.unsigned (Int.zero_ext 8 r).
Proof.
  pose proof (add8_u_range r) as H. apply Int.signed_eq_unsigned.
  unfold add8_u in H. change Int.max_signed with 2147483647; lia.
Qed.

Lemma division8_raw_unsigned remainder r t :
  Int.unsigned (division8_raw remainder r t) =
    division_numeric remainder (Int.unsigned (Int.zero_ext 8 r)) (Int.unsigned (Int.zero_ext 8 t)).
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range t) as HT.
  unfold add8_u in HR, HT.
  pose proof (division_numeric_range remainder _ _ 256 HR HT) as Hrange.
  unfold division8_raw. rewrite division8_zero_test.
  destruct (Z.eqb (Int.unsigned (Int.zero_ext 8 t)) 0) eqn:HZ.
  - unfold division_numeric. rewrite HZ. destruct remainder; [reflexivity|apply Int.unsigned_zero].
  - unfold division8_nonzero, division_numeric in *; rewrite HZ in *.
    destruct remainder; unfold Int.mods, Int.divs; rewrite !division8_signed.
    + rewrite Z.rem_mod_nonneg by (apply Z.eqb_neq in HZ; lia).
      apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia.
    + rewrite Z.quot_div_nonneg by (apply Z.eqb_neq in HZ; lia).
      apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia.
Qed.

Lemma division8_payload_unsigned remainder r t :
  Int.unsigned (division8_payload remainder r t) =
    division_numeric remainder (Int.unsigned (Int.zero_ext 8 r)) (Int.unsigned (Int.zero_ext 8 t)).
Proof.
  unfold division8_payload. rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  rewrite division8_raw_unsigned. apply Z.mod_small.
  apply division_numeric_range; apply add8_u_range.
Qed.

Lemma division_wide_raw_unsigned remainder r t :
  Int64.unsigned (division_wide_raw remainder r t) =
    division_numeric remainder (Int64.unsigned r) (Int64.unsigned t).
Proof.
  pose proof (Int64.unsigned_range r) as HR. pose proof (Int64.unsigned_range t) as HT.
  assert (HZ : Int64.eq Int64.zero t = Z.eqb (Int64.unsigned t) 0).
  { unfold Int64.eq. rewrite Int64.unsigned_zero.
    destruct (zeq 0 (Int64.unsigned t)); symmetry; [apply Z.eqb_eq|apply Z.eqb_neq]; lia. }
  unfold division_wide_raw. rewrite HZ.
  pose proof (division_numeric_range remainder _ _ Int64.modulus HR HT) as Hrange.
  destruct (Z.eqb (Int64.unsigned t) 0) eqn:HE.
  - unfold division_numeric. rewrite HE. destruct remainder; [reflexivity|apply Int64.unsigned_zero].
  - unfold division_numeric in *; rewrite HE in *.
    destruct remainder; unfold Int64.modu, Int64.divu; apply Int64.unsigned_repr;
      unfold Int64.max_unsigned; lia.
Qed.
