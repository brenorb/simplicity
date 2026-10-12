(** Size arithmetic of [simplicity_bitcoin_mallocTransaction] (bitcoin/env.c):
    with 32-bit input and output counts none of the four overflow checks
    fires, both paddings are zero, and the allocation is
    [488 + 160 * numInputs + 40 * numOutputs] bytes.  Pure integer facts. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.

Lemma u64 z : 0 <= z <= 18446744073709551615 -> Int64.unsigned (Int64.repr z) = z.
Proof. intros H. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. exact H. Qed.

Lemma u64_m1 : Int64.unsigned (Int64.repr (-1)) = 18446744073709551615.
Proof. reflexivity. Qed.

Section Counts.
Variables (ni no : Z).
Hypothesis Hni : 0 <= ni <= 4294967295.
Hypothesis Hno : 0 <= no <= 4294967295.

Lemma tx_mul_in : Int64.mul (Int64.repr ni) (Int64.repr 160) = Int64.repr (160 * ni).
Proof. unfold Int64.mul. rewrite (u64 ni), (u64 160) by lia. f_equal. lia. Qed.

Lemma tx_mul_out : Int64.mul (Int64.repr no) (Int64.repr 40) = Int64.repr (40 * no).
Proof. unfold Int64.mul. rewrite (u64 no), (u64 40) by lia. f_equal. lia. Qed.

Lemma tx_mul_one z : 0 <= z <= 4294967295 -> Int64.mul (Int64.repr 1) (Int64.repr z) = Int64.repr z.
Proof. intros H. unfold Int64.mul. rewrite (u64 1), (u64 z) by lia. f_equal. lia. Qed.

Lemma tx_size_in : Int64.add (Int64.repr 488) (Int64.repr (160 * ni)) = Int64.repr (488 + 160 * ni).
Proof. unfold Int64.add. rewrite (u64 488), (u64 (160 * ni)) by lia. reflexivity. Qed.

Lemma tx_size_out :
  Int64.add (Int64.repr (488 + 160 * ni)) (Int64.repr (40 * no)) = Int64.repr (488 + 160 * ni + 40 * no).
Proof. unfold Int64.add. rewrite (u64 (488 + 160 * ni)), (u64 (40 * no)) by lia. reflexivity. Qed.

Lemma tx_add_zero z : Int64.add (Int64.repr z) (Int64.repr 0) = Int64.repr z.
Proof. apply Int64.add_zero. Qed.

Lemma tx_div_in : Int64.ltu (Int64.divu (Int64.repr (-1)) (Int64.repr 160)) (Int64.repr ni) = false.
Proof.
  unfold Int64.ltu. apply zlt_false. rewrite (u64 ni) by lia.
  change (Int64.unsigned (Int64.divu (Int64.repr (-1)) (Int64.repr 160))) with 115292150460684697. lia.
Qed.

Lemma tx_div_out : Int64.ltu (Int64.divu (Int64.repr (-1)) (Int64.repr 40)) (Int64.repr no) = false.
Proof.
  unfold Int64.ltu. apply zlt_false. rewrite (u64 no) by lia.
  change (Int64.unsigned (Int64.divu (Int64.repr (-1)) (Int64.repr 40))) with 461168601842738790. lia.
Qed.

Lemma tx_room z y : 0 <= z <= 1000000000000 -> 0 <= y <= 1000000000000 ->
  Int64.ltu (Int64.sub (Int64.repr (-1)) (Int64.repr z)) (Int64.repr y) = false.
Proof.
  intros Hz Hy. unfold Int64.ltu. apply zlt_false. unfold Int64.sub.
  rewrite u64_m1, (u64 z), (u64 y) by lia. rewrite u64 by lia. lia.
Qed.

Lemma tx_pad2 :
  Int64.modu (Int64.sub (Int64.repr 8) (Int64.modu (Int64.repr (488 + 160 * ni)) (Int64.repr 8))) (Int64.repr 8) =
    Int64.repr 0.
Proof.
  assert (HM : (488 + 160 * ni) mod 8 = 0).
  { replace (488 + 160 * ni) with ((61 + 20 * ni) * 8) by lia. apply Z_mod_mult. }
  unfold Int64.modu at 2. rewrite (u64 (488 + 160 * ni)), (u64 8) by lia. rewrite HM.
  unfold Int64.sub. rewrite (u64 8), (u64 0) by lia.
  unfold Int64.modu. rewrite (u64 (8 - 0)), (u64 8) by lia. reflexivity.
Qed.

Lemma tx_input_ptr :
  Ptrofs.add (Ptrofs.repr 488)
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.add (Int64.repr (160 * ni)) (Int64.repr 0)))) =
    Ptrofs.repr (488 + 160 * ni).
Proof.
  rewrite tx_add_zero. unfold Ptrofs.of_int64. rewrite (u64 (160 * ni)) by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.add.
  rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.
End Counts.

Lemma tx_first_ptr :
  Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.add (Int64.repr 488) (Int64.repr 0)))) = Ptrofs.repr 488.
Proof. vm_compute. reflexivity. Qed.
