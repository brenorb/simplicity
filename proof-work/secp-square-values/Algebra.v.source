(** Shared equality rules for the real two-word machine accumulators. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_multiply_checkpoint_machine C.jet_secp_multiply_secondvalues_accum.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma pair_value_injective a b : pair_value a = pair_value b -> a = b.
Proof.
  destruct a as [al ah], b as [bl bh]; unfold pair_value; cbn [fst snd].
  intro H.
  assert (EL : Int64.unsigned al = Int64.unsigned bl).
  { apply (f_equal (fun z => z mod Int64.modulus)) in H.
    rewrite (Z.mul_comm Int64.modulus (Int64.unsigned ah)),
      (Z.mul_comm Int64.modulus (Int64.unsigned bh)), !Z.mod_add in H
      by (pose proof Int64.modulus_pos; lia).
    rewrite !Z.mod_small in H by apply Int64.unsigned_range; exact H. }
  assert (EH : Int64.unsigned ah = Int64.unsigned bh).
  { pose proof Int64.modulus_pos; nia. }
  apply (f_equal Int64.repr) in EL; apply (f_equal Int64.repr) in EH.
  rewrite !Int64.repr_unsigned in EL, EH; subst; reflexivity.
Qed.

Lemma accumulate_mod ps s : pair_value (accumulate s ps) =
  (pair_value s + products ps) mod (Int64.modulus * Int64.modulus).
Proof.
  revert s; induction ps as [|[a b] ps IH]; intro s; cbn [accumulate products].
  - rewrite Z.add_0_r, Z.mod_small; [reflexivity|apply pair_value_range].
  - rewrite IH, machine_accum_value, Z.add_mod_idemp_l by (pose proof Int64.modulus_pos; nia).
    f_equal; ring.
Qed.

Lemma accumulate_products_equal ps qs s : products ps = products qs ->
  accumulate s ps = accumulate s qs.
Proof. intro H; apply pair_value_injective; rewrite !accumulate_mod, H; reflexivity. Qed.

Lemma product_as_accumulate a b : machine_product a b =
  accumulate (Int64.zero, Int64.zero) [(a,b)].
Proof.
  apply pair_value_injective; rewrite accumulate_mod, machine_product_value.
  change (Int64.unsigned a * Int64.unsigned b =
    (0 + (Int64.unsigned a * Int64.unsigned b + 0)) mod (Int64.modulus * Int64.modulus)).
  rewrite !Z.add_0_l, !Z.add_0_r, Z.mod_small; [reflexivity|].
  pose proof (Int64.unsigned_range a); pose proof (Int64.unsigned_range b).
  pose proof Int64.modulus_pos; nia.
Qed.

Definition twice a := Int64.mul a (Int64.repr 2).
Lemma twice_unsigned a : Int64.unsigned a < 72057594037927936 ->
  Int64.unsigned (twice a) = 2 * Int64.unsigned a.
Proof.
  intro H; unfold twice, Int64.mul.
  change (Int64.unsigned (Int64.repr (Int64.unsigned a * 2)) = 2 * Int64.unsigned a).
  rewrite Int64.unsigned_repr; [ring|].
  pose proof (Int64.unsigned_range a).
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.
