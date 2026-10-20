(** Compact machine operations and exact numeric observations, including wrap. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers Values.
Require Import C.jet_sx_expr C.jet_secp_u64_carry C.jet_secp_umul128_numeric.
Require Import C.jet_secp_u128_accum_mul_numeric.
Require Import C.jet_secp_multiply_shift_shift C.jet_secp_multiply_shift_numeric C.jet_secp_multiply_checkpoint_ops.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition word_den rho beta x := il (den rho beta x).
Definition pair_den rho beta (s : sx * sx) := (word_den rho beta (fst s), word_den rho beta (snd s)).
Definition pair_value (s : int64 * int64) := Int64.unsigned (fst s) + Int64.modulus * Int64.unsigned (snd s).
Definition machine_product a b := (umul128_lo_machine a b, umul128_hi_machine a b).
Definition machine_carry lo a := Int64.repr (Int.signed (if Int64.ltu lo a then Int.one else Int.zero)).
Definition machine_accum (s : int64 * int64) a b :=
  let p := machine_product a b in let lo := Int64.add (fst s) (fst p) in
  (lo, Int64.add (snd s) (Int64.add (snd p) (machine_carry lo (fst p)))).
Definition machine_accum_word (s : int64 * int64) a :=
  let lo := Int64.add (fst s) a in (lo, Int64.add (snd s) (machine_carry lo a)).
Definition machine_shift52 (s : int64 * int64) := (shift52_low (fst s) (snd s), shift52_high (snd s)).
Definition machine_shift64 (s : int64 * int64) := (snd s, Int64.zero).

Lemma sx_product_machine rho beta a b : pair_den rho beta (sx_product a b) =
  machine_product (word_den rho beta a) (word_den rho beta b).
Proof. reflexivity. Qed.
Lemma sx_accum_machine rho beta s a b : pair_den rho beta (sx_accum s a b) =
  machine_accum (pair_den rho beta s) (word_den rho beta a) (word_den rho beta b).
Proof. reflexivity. Qed.
Lemma sx_accum_word_machine rho beta s a : pair_den rho beta (sx_accum_word s a) =
  machine_accum_word (pair_den rho beta s) (word_den rho beta a).
Proof. reflexivity. Qed.
Lemma sx_shift52_machine rho beta s : pair_den rho beta (sx_shift52 s) = machine_shift52 (pair_den rho beta s).
Proof. reflexivity. Qed.
Lemma sx_shift64_machine rho beta s : pair_den rho beta (sx_shift64 s) = machine_shift64 (pair_den rho beta s).
Proof. reflexivity. Qed.

Lemma pair_low_den rho beta s ma : pair_den rho beta s = ma -> isk KL (fst s) = true ->
  den rho beta (fst s) = Vlong (fst ma).
Proof.
  intros H HK; rewrite (den_KL rho beta _ HK).
  apply (f_equal (@fst int64 int64)) in H; cbn [pair_den fst] in H.
  unfold word_den in H; rewrite H; reflexivity.
Qed.
Lemma pair_high_den rho beta s ma : pair_den rho beta s = ma -> isk KL (snd s) = true ->
  den rho beta (snd s) = Vlong (snd ma).
Proof.
  intros H HK; rewrite (den_KL rho beta _ HK).
  apply (f_equal (@snd int64 int64)) in H; cbn [pair_den snd] in H.
  unfold word_den in H; rewrite H; reflexivity.
Qed.

Lemma pair_value_range s : 0 <= pair_value s < Int64.modulus * Int64.modulus.
Proof.
  unfold pair_value; pose proof (Int64.unsigned_range (fst s)); pose proof (Int64.unsigned_range (snd s)).
  pose proof Int64.modulus_pos; nia.
Qed.
Lemma machine_product_value a b : pair_value (machine_product a b) = Int64.unsigned a * Int64.unsigned b.
Proof.
  destruct (umul128_unsigned_outputs a b) as [HH HL]. unfold pair_value, machine_product; cbn [fst snd].
  rewrite HH, HL. pose proof (Z.div_mod (Int64.unsigned a * Int64.unsigned b) Int64.modulus ltac:(discriminate)); lia.
Qed.
Lemma machine_accum_value s a b : pair_value (machine_accum s a b) =
  (pair_value s + Int64.unsigned a * Int64.unsigned b) mod (Int64.modulus * Int64.modulus).
Proof.
  pose proof (accum_mul_numeric_value (fun n => match n with 0%nat => a | 1%nat => b | 2%nat => fst s | _ => snd s end)) as H.
  change (Int64.unsigned (snd (machine_accum s a b)) * Int64.modulus +
    Int64.unsigned (fst (machine_accum s a b)) =
    (Int64.unsigned (snd s) * Int64.modulus + Int64.unsigned (fst s) +
     Int64.unsigned a * Int64.unsigned b) mod (Int64.modulus * Int64.modulus)) in H.
  unfold pair_value.
  replace (Int64.unsigned (fst (machine_accum s a b)) + Int64.modulus * Int64.unsigned (snd (machine_accum s a b))) with
    (Int64.unsigned (snd (machine_accum s a b)) * Int64.modulus + Int64.unsigned (fst (machine_accum s a b))) by ring.
  replace (Int64.unsigned (fst s) + Int64.modulus * Int64.unsigned (snd s)) with
    (Int64.unsigned (snd s) * Int64.modulus + Int64.unsigned (fst s)) by ring.
  exact H.
Qed.
Lemma machine_accum_exact s a b : pair_value s + Int64.unsigned a * Int64.unsigned b < Int64.modulus * Int64.modulus ->
  pair_value (machine_accum s a b) = pair_value s + Int64.unsigned a * Int64.unsigned b.
Proof.
  intro HB; rewrite machine_accum_value. apply Z.mod_small; split; [|exact HB].
  pose proof (pair_value_range s); pose proof (Int64.unsigned_range a); pose proof (Int64.unsigned_range b); nia.
Qed.
Lemma machine_shift52_value s : pair_value (machine_shift52 s) = pair_value s / 4503599627370496.
Proof.
  pose proof (shift52_numeric (fst s) (snd s)) as H.
  unfold pair_value, machine_shift52; cbn [fst snd].
  rewrite Z.add_comm, Z.mul_comm.
  replace (Int64.unsigned (fst s) + Int64.modulus * Int64.unsigned (snd s)) with
    (Int64.unsigned (snd s) * Int64.modulus + Int64.unsigned (fst s)) by ring.
  exact H.
Qed.
Lemma machine_shift64_value s : pair_value (machine_shift64 s) = pair_value s / Int64.modulus.
Proof.
  unfold pair_value, machine_shift64; cbn [fst snd]. rewrite Int64.unsigned_zero, Z.mul_0_r, Z.add_0_r.
  apply Z.div_unique with (Int64.unsigned (fst s)); [left; apply Int64.unsigned_range|ring].
Qed.

Lemma machine_mask52_value x :
  Int64.unsigned (Int64.and x (Int64.repr 4503599627370495)) = Int64.unsigned x mod 4503599627370496.
Proof.
  assert (HP : Int64.is_power2 (Int64.repr 4503599627370496) = Some (Int64.repr 52)) by (vm_compute; reflexivity).
  pose proof (Int64.modu_and x _ _ HP) as H.
  change (Int64.modu x (Int64.repr 4503599627370496) = Int64.and x (Int64.repr 4503599627370495)) in H.
  rewrite <- H; unfold Int64.modu.
  change (Int64.unsigned (Int64.repr (Int64.unsigned x mod 4503599627370496)) = Int64.unsigned x mod 4503599627370496).
  apply Int64.unsigned_repr.
  pose proof (Z.mod_pos_bound (Int64.unsigned x) 4503599627370496 ltac:(lia));
    change Int64.max_unsigned with 18446744073709551615; lia.
Qed.
