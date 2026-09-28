(** Width-generic arithmetic of the integer view of [Word n].

    [Word n] has [2^n] bits.  These lemmas replace the per-width copies of the
    range and high-bit facts used by the 16-, 32- and 64-bit readers and by the
    canonical-encoding layer.  They concern the logical value only, not the
    carrier type of any C function: the sub-64-bit and 64-bit carriers differ in
    when truncation happens, which is handled in the width-specific bridges. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word.
Local Open Scope Z_scope.

Lemma word_bitSize n : ToZ.Theory.bitSize (WordToZ n) = Nat.pow 2 n.
Proof.
  apply Nat2Z.inj. rewrite bitSize_Word, two_power_nat_equiv, Nat2Z.inj_pow.
  reflexivity.
Qed.

Lemma word_toZ_mod n (x : Ty.tySem (Word n)) :
  @toZ (WordToZ n) x mod 2 ^ Z.of_nat (Nat.pow 2 n) = @toZ (WordToZ n) x.
Proof.
  pose proof (@toZ_mod (WordToZ n) x) as H.
  rewrite two_power_nat_equiv, word_bitSize in H. symmetry. exact H.
Qed.

Lemma word_toZ_range n (x : Ty.tySem (Word n)) :
  0 <= @toZ (WordToZ n) x < 2 ^ Z.of_nat (Nat.pow 2 n).
Proof.
  rewrite <- word_toZ_mod. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.


(** Bits at or above the word width are zero. *)
Lemma word_toZ_high_bits n (x : Ty.tySem (Word n)) j :
  Z.of_nat (Nat.pow 2 n) <= j -> Z.testbit (@toZ (WordToZ n) x) j = false.
Proof.
  intros Hj. rewrite <- word_toZ_mod. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma word_fromZ_mod n z :
  @fromZ (WordToZ n) (z mod 2 ^ Z.of_nat (Nat.pow 2 n)) = @fromZ (WordToZ n) z.
Proof.
  rewrite <- (@from_toZ (WordToZ n) (@fromZ (WordToZ n) z)).
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize. reflexivity.
Qed.

(** Decoding a machine integer to a word only depends on its low bits. *)
Lemma word_fromZ_bits n (x : Ty.tySem (Word n)) z :
  @fromZ (WordToZ n) z = x <->
  (forall j, 0 <= j < Z.of_nat (Nat.pow 2 n) ->
    Z.testbit z j = Z.testbit (@toZ (WordToZ n) x) j).
Proof.
  split.
  - intros <- j Hj. rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
    symmetry. apply Z.mod_pow2_bits_low. lia.
  - intros H. rewrite <- word_fromZ_mod.
    replace (z mod 2 ^ Z.of_nat (Nat.pow 2 n)) with (@toZ (WordToZ n) x).
    + apply from_toZ.
    + rewrite <- word_toZ_mod. apply Z.bits_inj_iff'. intros k Hk.
      destruct (Z.lt_ge_cases k (Z.of_nat (Nat.pow 2 n))) as [Hlt|Hge].
      * rewrite !Z.mod_pow2_bits_low by exact Hlt. symmetry. apply H. lia.
      * rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma nth_error_seq_in start n i :
  (i < n)%nat -> nth_error (List.seq start n) i = Some (start + i)%nat.
Proof.
  revert start i. induction n as [|n IH]; intros start i Hi; [lia|].
  destruct i as [|i]; cbn.
  - f_equal; lia.
  - rewrite IH by lia. f_equal; lia.
Qed.

