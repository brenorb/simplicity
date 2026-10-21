(** Value and range bookkeeping for actual fe_add results, for repeated
    addition in point doubling.  Bounds are derived at callers, not assumed
    as intermediate outputs of the public jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_field_add_scaled C.jet_secp_field_mul_small C.jet_secp_square_columns
  C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_scaled_bounds (n : Z) (w : nat -> int64) :=
  forall i, (i<5)%nat -> Int64.unsigned (w i)<
    n*(if Nat.eqb i 4 then 562949953421312 else 4503599627370496).

Lemma field_tight_scaled w : mul_small_input_bounds w -> field_scaled_bounds 1 w.
Proof.
  intros HB i HI;specialize (HB i HI).
  change (Int64.unsigned (w i)<1*(if Nat.eqb i 4 then 562949953421312 else 4503599627370496));lia.
Qed.

Lemma field_sum_scaled_no_overflow n m a b :
  0<=n -> 0<=m -> n+m<=8 -> field_scaled_bounds n a -> field_scaled_bounds m b ->
  forall i, (i<5)%nat -> Int64.unsigned (a i)+Int64.unsigned (b i)<=Int64.max_unsigned.
Proof.
  intros HN HM HNM HA HB i HI;pose proof (HA i HI);pose proof (HB i HI).
  change Int64.max_unsigned with 18446744073709551615;destruct (Nat.eqb i 4);nia.
Qed.

Lemma field_sum_scaled_bounds n m a b :
  0<=n -> 0<=m -> n+m<=8 -> field_scaled_bounds n a -> field_scaled_bounds m b ->
  field_scaled_bounds (n+m) (field_sum_words a b).
Proof.
  intros HN HM HNM HA HB i HI.
  rewrite field_sum_unsigned by exact (field_sum_scaled_no_overflow n m a b HN HM HNM HA HB i HI).
  pose proof (HA i HI);pose proof (HB i HI);destruct (Nat.eqb i 4);nia.
Qed.

Lemma field_sum_exact_value a b :
  (forall i, (i<5)%nat -> Int64.unsigned (a i)+Int64.unsigned (b i)<=Int64.max_unsigned) ->
  radix_value (field_sum_words a b)=radix_value a+radix_value b.
Proof.
  intro HB;rewrite !radix_value_matches_normalizer;unfold fe_val.
  rewrite (field_sum_unsigned a b 0%nat (HB 0%nat ltac:(lia))),
    (field_sum_unsigned a b 1%nat (HB 1%nat ltac:(lia))),
    (field_sum_unsigned a b 2%nat (HB 2%nat ltac:(lia))),
    (field_sum_unsigned a b 3%nat (HB 3%nat ltac:(lia))),
    (field_sum_unsigned a b 4%nat (HB 4%nat ltac:(lia)));ring.
Qed.

Lemma field_scaled_loose n w : 0<=n<=8 -> field_scaled_bounds n w -> square_input_bounds w.
Proof.
  intros HN HB i HI;pose proof (HB i HI);destruct (Nat.eqb i 4);nia.
Qed.

Lemma field_sum_twice_value a b : mul_small_input_bounds a -> mul_small_input_bounds b ->
  radix_value (field_sum_words (field_sum_words a b) b)=radix_value a+2*radix_value b /\
  field_scaled_bounds 3 (field_sum_words (field_sum_words a b) b).
Proof.
  intros HA HB;pose proof (field_tight_scaled a HA) as A;pose proof (field_tight_scaled b HB) as B.
  pose proof (field_sum_scaled_bounds 1 1 a b ltac:(lia) ltac:(lia) ltac:(lia) A B) as AB.
  split.
  - rewrite (field_sum_exact_value (field_sum_words a b) b
      (field_sum_scaled_no_overflow 2 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) AB B)),
      (field_sum_exact_value a b
      (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) A B));ring.
  - exact (field_sum_scaled_bounds 2 1 (field_sum_words a b) b ltac:(lia) ltac:(lia) ltac:(lia) AB B).
Qed.
