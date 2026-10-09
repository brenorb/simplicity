(** Exact integer OR/zero test for canonical five-limb field storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_predicate_wide_exec C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_b32_exec C.jet_secp_field_zero.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma int64_or_zero_iff x y :
  Int64.or x y = Int64.zero <-> x = Int64.zero /\ y = Int64.zero.
Proof.
  split.
  - intro HOr; split.
    + rewrite <- (Int64.and_or_absorb x y). rewrite HOr; apply Int64.and_zero.
    + rewrite Int64.or_commut in HOr.
      rewrite <- (Int64.and_or_absorb y x). rewrite HOr; apply Int64.and_zero.
  - intros [-> ->]; apply Int64.or_zero.
Qed.
Lemma int64_or_zero_bool x y :
  Int64.eq (Int64.or x y) Int64.zero =
    andb (Int64.eq x Int64.zero) (Int64.eq y Int64.zero).
Proof.
  apply Bool.eq_true_iff_eq. rewrite Bool.andb_true_iff.
  split.
  - intro H; apply Int64.same_if_eq in H; apply int64_or_zero_iff in H.
    destruct H as [-> ->]; split; apply Int64.eq_true.
  - intros [HX HY]; apply Int64.same_if_eq in HX; apply Int64.same_if_eq in HY.
    subst x y; rewrite Int64.or_zero; apply Int64.eq_true.
Qed.
Lemma int64_repr_zero_bool value :
  0 <= value <= Int64.max_unsigned ->
  Int64.eq (Int64.repr value) Int64.zero = Z.eqb value 0.
Proof.
  intro H; rewrite int64_eq_numeric, Int64.unsigned_repr, Int64.unsigned_zero; [reflexivity|exact H].
Qed.
Lemma field_or_canonical_zero value rc :
  0 <= value < 2 ^ 256 ->
  Int64.eq (field_or_value (write_fe_rho value rc)) Int64.zero = Z.eqb value 0.
Proof.
  intro HValue.
  destruct (fe_limbs_of_ok value HValue) as [HBounds HReconstruct].
  unfold fe_limbs_ok in HBounds.
  unfold field_or_value, write_fe_rho, limb_rho, fe_limbs_of.
  cbn [nth].
  rewrite !int64_or_zero_bool.
  rewrite !int64_repr_zero_bool by
    (change Int64.max_unsigned with 18446744073709551615; intuition lia).
  apply Bool.eq_true_iff_eq.
  rewrite !Bool.andb_true_iff, !Z.eqb_eq.
  unfold fe_val in HReconstruct.
  change (2 ^ 52) with 4503599627370496 in *.
  change (2 ^ 104) with 20282409603651670423947251286016 in *.
  change (2 ^ 156) with 91343852333181432387730302044767688728495783936 in *.
  change (2 ^ 208) with 411376139330301510538742295639337626245683966408394965837152256 in *.
  intuition lia.
Qed.
