(** Concrete valuations for the real +7 / weak-normalize / equality calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_fe_math C.jet_secp_field_add_initial C.jet_secp_b32_exec.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_curve_equal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition curve_shift_words (w : nat -> int64) (n : nat) := w (n-1)%nat.
Definition curve_weak_words a b c d e (i : nat) :=
  nth i [Int64.repr a;Int64.repr b;Int64.repr c;Int64.repr d;Int64.repr e] Int64.zero.
Definition curve_equal_rho (a b : nat -> int64) (n : nat) :=
  nth n (Int64.zero :: words5 a ++ words5 b) Int64.zero.

Lemma curve_shift_field w : field_values (curve_shift_words w) 1 = words5 w.
Proof. reflexivity. Qed.
Lemma curve_weak_field a b c d e :
  words5 (curve_weak_words a b c d e) = map Int64.repr [a;b;c;d;e].
Proof. reflexivity. Qed.
Lemma curve_equal_first a b : field_values (curve_equal_rho a b) 1 = words5 a.
Proof. reflexivity. Qed.
Lemma curve_equal_second a b : field_values (curve_equal_rho a b) 6 = words5 b.
Proof. reflexivity. Qed.

Lemma curve_equal_first_value a b :
  fe_val (Int64.unsigned (curve_equal_rho a b 1%nat))
    (Int64.unsigned (curve_equal_rho a b 2%nat)) (Int64.unsigned (curve_equal_rho a b 3%nat))
    (Int64.unsigned (curve_equal_rho a b 4%nat)) (Int64.unsigned (curve_equal_rho a b 5%nat)) = radix_value a.
Proof. rewrite radix_value_matches_normalizer; reflexivity. Qed.
Lemma curve_equal_second_value a b :
  fe_val (Int64.unsigned (curve_equal_rho a b 6%nat))
    (Int64.unsigned (curve_equal_rho a b 7%nat)) (Int64.unsigned (curve_equal_rho a b 8%nat))
    (Int64.unsigned (curve_equal_rho a b 9%nat)) (Int64.unsigned (curve_equal_rho a b 10%nat)) = radix_value b.
Proof. rewrite radix_value_matches_normalizer; reflexivity. Qed.

Lemma curve_equal_initial a b m ba bb : ba<>bb ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (curve_equal_rho a b) [(ba,0);(bb,0)] curve_equal_regs m.
Proof.
  intros HD HA HB HFA HFB. apply two_region_rep_separate; [reflexivity|exact HD| |].
  - apply region_with_freeable.
    + apply field_region_from_values; rewrite curve_equal_first; exact HA.
    + reflexivity.
    + reflexivity.
    + exact HFA.
    + apply field_region_storage_size.
  - apply region_with_freeable.
    + apply field_region_from_values; rewrite curve_equal_second; exact HB.
    + reflexivity.
    + reflexivity.
    + exact HFB.
    + apply field_region_storage_size.
Qed.

Lemma curve_equal_inputs_bounded a b :
  (forall i, (i < 5)%nat -> Int64.unsigned (a i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i < 5)%nat -> Int64.unsigned (b i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  forall n, fst (curve_equal_bounds n) <= Int64.unsigned (curve_equal_rho a b n) <= snd (curve_equal_bounds n).
Proof.
  intros HA HB n. split; [apply Int64.unsigned_range_2|].
  pose proof (HA 0%nat ltac:(lia)); pose proof (HA 1%nat ltac:(lia));
  pose proof (HA 2%nat ltac:(lia)); pose proof (HA 3%nat ltac:(lia)); pose proof (HA 4%nat ltac:(lia));
  pose proof (HB 0%nat ltac:(lia)); pose proof (HB 1%nat ltac:(lia));
  pose proof (HB 2%nat ltac:(lia)); pose proof (HB 3%nat ltac:(lia)); pose proof (HB 4%nat ltac:(lia)).
  cbn [Nat.eqb] in *.
  do 11 (destruct n as [|n];
    [cbn [curve_equal_rho curve_equal_bounds words5 nth app Nat.eqb orb snd];
     rewrite ?Int64.unsigned_zero; lia|]).
  destruct n; cbn [curve_equal_rho curve_equal_bounds words5 nth app Nat.eqb orb snd];
    rewrite Int64.unsigned_zero; lia.
Qed.

Lemma curve_weak_words_value a b c d e :
  0 <= a <= 4503599627370495 -> 0 <= b <= 4503599627370495 ->
  0 <= c <= 4503599627370495 -> 0 <= d <= 4503599627370495 ->
  0 <= e <= 281474976710912 ->
  radix_value (curve_weak_words a b c d e) = fe_val a b c d e /\
  (forall i, (i < 5)%nat -> Int64.unsigned (curve_weak_words a b c d e i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496).
Proof.
  intros HA HB HC HD HE. split.
  - rewrite radix_value_matches_normalizer. cbn [curve_weak_words nth].
    rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    reflexivity.
  - intros i HI. destruct i as [|[|[|[|[|i]]]]]; try lia;
      cbn [curve_weak_words nth Nat.eqb];
      rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia); lia.
Qed.
