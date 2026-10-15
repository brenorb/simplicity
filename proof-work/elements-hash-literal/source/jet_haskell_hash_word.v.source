(** Explicit four-limb Simplicity.Word.Word256 model and byte append.
    Every limb represents one unsigned Haskell Word64. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Zbits Integers.
Require Import Simplicity.Word Simplicity.Digest C.jet_haskell_word_conversion C.jet_word_repr.
Require Import sha.general_lemmas.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition haskell_word64_modulus : Z := 18446744073709551616.
Definition haskell_word256_modulus : Z :=
  haskell_word64_modulus * haskell_word64_modulus *
  haskell_word64_modulus * haskell_word64_modulus.

Record haskell_word256 := HaskellWord256 { hw3 : Z; hw2 : Z; hw1 : Z; hw0 : Z }.

Definition haskell_word256_valid w :=
  Forall (fun z => 0 <= z < haskell_word64_modulus) [hw3 w; hw2 w; hw1 w; hw0 w].

Definition haskell_word256_from_integer z :=
  let a1 := z / haskell_word64_modulus in
  let a2 := a1 / haskell_word64_modulus in
  let a3 := a2 / haskell_word64_modulus in
  HaskellWord256 (a3 mod haskell_word64_modulus) (a2 mod haskell_word64_modulus)
    (a1 mod haskell_word64_modulus) (z mod haskell_word64_modulus).

Definition haskell_word256_integer w :=
  hw0 w + haskell_word64_modulus *
    (hw1 w + haskell_word64_modulus * (hw2 w + haskell_word64_modulus * hw3 w)).

Definition haskell_word256_or x y :=
  HaskellWord256 (Z.lor (hw3 x) (hw3 y)) (Z.lor (hw2 x) (hw2 y))
    (Z.lor (hw1 x) (hw1 y)) (Z.lor (hw0 x) (hw0 y)).

Definition haskell_word256_shift8 w :=
  haskell_word256_from_integer (Z.shiftl (haskell_word256_integer w) 8).

Definition haskell_be256_step w (b : byte) :=
  haskell_word256_or (haskell_word256_shift8 w)
    (haskell_word256_from_integer (Byte.unsigned b)).

Lemma haskell_word64_modulus_positive : 0 < haskell_word64_modulus.
Proof. unfold haskell_word64_modulus; lia. Qed.

Lemma haskell_word256_modulus_positive : 0 < haskell_word256_modulus.
Proof.
  unfold haskell_word256_modulus.
  repeat apply Z.mul_pos_pos; exact haskell_word64_modulus_positive.
Qed.

Lemma four_limbs_horner_mod B z : 0 < B ->
  z mod B + B * ((z / B) mod B + B *
    (((z / B) / B) mod B + B * ((((z / B) / B) / B) mod B))) = z mod (B * B * B * B).
Proof.
  intro HB. rewrite !Z.mod_eq by nia. rewrite !Z.div_div by nia. ring.
Qed.

Lemma haskell_word256_from_integer_unsigned z :
  haskell_word256_integer (haskell_word256_from_integer z) = z mod haskell_word256_modulus.
Proof.
  change (z mod haskell_word64_modulus + haskell_word64_modulus *
    ((z / haskell_word64_modulus) mod haskell_word64_modulus + haskell_word64_modulus *
    (((z / haskell_word64_modulus) / haskell_word64_modulus) mod haskell_word64_modulus +
      haskell_word64_modulus * ((((z / haskell_word64_modulus) / haskell_word64_modulus) /
        haskell_word64_modulus) mod haskell_word64_modulus))) = z mod haskell_word256_modulus).
  unfold haskell_word256_modulus.
  apply four_limbs_horner_mod. exact haskell_word64_modulus_positive.
Qed.

Lemma haskell_word256_from_integer_valid z :
  haskell_word256_valid (haskell_word256_from_integer z).
Proof.
  unfold haskell_word256_valid, haskell_word256_from_integer.
  cbv beta iota zeta delta [hw0 hw1 hw2 hw3].
  repeat (apply Forall_cons; [apply Z.mod_pos_bound; exact haskell_word64_modulus_positive|]).
  constructor.
Qed.

Lemma haskell_shift_or_byte x b : 0 <= b < 256 ->
  Z.lor (Z.shiftl x 8) b = x * 256 + b.
Proof.
  intros Hb.
  replace (x * 256) with (Z.shiftl x 8) by
    (rewrite Zshiftl_mul_two_p by lia; reflexivity).
  apply Z.bits_inj_iff'. intros i Hi. rewrite Z.lor_spec.
  symmetry. apply Z_add_is_or; [exact Hi|].
  intros j Hj. destruct (Z.lt_ge_cases j 8) as [Hlt|Hge].
  - rewrite Z.shiftl_spec by lia. rewrite Z.testbit_neg_r by lia. reflexivity.
  - rewrite (Ztestbit_above 8 b j Hb ltac:(lia)). apply andb_false_r.
Qed.

Lemma haskell_append_byte_div x b d : 0 <= b < 256 -> 0 < d ->
  (x * 256 + b) / (d * 256) = x / d.
Proof.
  intros Hb Hd. symmetry.
  apply Z.div_unique with (r := (x mod d) * 256 + b).
  - left. pose proof (Z.mod_pos_bound x d Hd). nia.
  - pose proof (Z.div_mod x d ltac:(lia)). nia.
Qed.

Lemma haskell_append_byte_mod x b d : 0 <= b < 256 -> 0 < d ->
  (x * 256 + b) mod (d * 256) = (x mod d) * 256 + b.
Proof.
  intros Hb Hd. symmetry.
  apply Z.mod_unique with (q := x / d).
  - left. pose proof (Z.mod_pos_bound x d Hd). nia.
  - pose proof (Z.div_mod x d ltac:(lia)). nia.
Qed.

Definition haskell_word64_byte_quotient : Z := 72057594037927936.

Lemma haskell_word64_byte_split :
  haskell_word64_modulus = haskell_word64_byte_quotient * 256.
Proof. reflexivity. Qed.

Lemma haskell_word256_from_byte b : 0 <= b < 256 ->
  haskell_word256_from_integer b = HaskellWord256 0 0 0 b.
Proof.
  intros Hb. assert (HB : 0 <= b < haskell_word64_modulus) by
    (unfold haskell_word64_modulus; lia).
  assert (HD : b / haskell_word64_modulus = 0) by (apply Z.div_small; exact HB).
  unfold haskell_word256_from_integer. rewrite HD.
  change (HaskellWord256 0 0 0 (b mod haskell_word64_modulus) = HaskellWord256 0 0 0 b).
  rewrite Z.mod_small by exact HB. reflexivity.
Qed.

Lemma haskell_word256_or_byte x b : 0 <= b < 256 ->
  haskell_word256_or (haskell_word256_from_integer (x * 256))
    (haskell_word256_from_integer b) = haskell_word256_from_integer (x * 256 + b).
Proof.
  intros Hb.
  assert (HD : 0 < haskell_word64_byte_quotient) by
    (unfold haskell_word64_byte_quotient; lia).
  assert (HQ0 : (x * 256) / haskell_word64_modulus = x / haskell_word64_byte_quotient).
  { rewrite haskell_word64_byte_split.
    replace (x * 256) with (x * 256 + 0) at 1 by ring.
    apply haskell_append_byte_div; lia. }
  assert (HQb : (x * 256 + b) / haskell_word64_modulus = x / haskell_word64_byte_quotient).
  { rewrite haskell_word64_byte_split. apply haskell_append_byte_div; assumption. }
  assert (HR0 : (x * 256) mod haskell_word64_modulus = (x mod haskell_word64_byte_quotient) * 256).
  { rewrite haskell_word64_byte_split.
    replace (x * 256) with (x * 256 + 0) at 1 by ring.
    rewrite haskell_append_byte_mod by lia. ring. }
  assert (HRb : (x * 256 + b) mod haskell_word64_modulus = (x mod haskell_word64_byte_quotient) * 256 + b).
  { rewrite haskell_word64_byte_split. apply haskell_append_byte_mod; assumption. }
  rewrite (haskell_word256_from_byte b Hb).
  unfold haskell_word256_or, haskell_word256_from_integer.
  cbv beta iota zeta delta [hw0 hw1 hw2 hw3].
  rewrite HQ0, HQb, HR0, HRb, !Z.lor_0_r.
  f_equal. pose proof (haskell_shift_or_byte (x mod haskell_word64_byte_quotient) b Hb) as H.
  rewrite Zshiftl_mul_two_p in H by lia. exact H.
Qed.

Lemma haskell_be256_step_append w b :
  haskell_be256_step w b = haskell_word256_from_integer
    (haskell_word256_integer w * 256 + Byte.unsigned b).
Proof.
  unfold haskell_be256_step, haskell_word256_shift8.
  rewrite Zshiftl_mul_two_p by lia.
  apply haskell_word256_or_byte. exact (Byte.unsigned_range b).
Qed.

Lemma haskell_be256_step_valid w b : haskell_word256_valid (haskell_be256_step w b).
Proof. rewrite haskell_be256_step_append. apply haskell_word256_from_integer_valid. Qed.

Fixpoint haskell_be256_run (bytes : list byte) (w : haskell_word256) : haskell_word256 :=
  match bytes with
  | nil => w
  | b :: rest => haskell_be256_run rest (haskell_be256_step w b)
  end.

Fixpoint be_integer_bytes (bytes : list byte) (z : Z) : Z :=
  match bytes with
  | nil => z
  | b :: rest => be_integer_bytes rest (z * 256 + Byte.unsigned b)
  end.

Lemma haskell_be256_run_valid bytes : forall w,
  haskell_word256_valid w -> haskell_word256_valid (haskell_be256_run bytes w).
Proof.
  induction bytes as [|b rest IH]; intros w HW; cbn [haskell_be256_run]; [exact HW|].
  apply IH. apply haskell_be256_step_valid.
Qed.

Lemma haskell_append_byte_mod_congruent x y b :
  x mod haskell_word256_modulus = y mod haskell_word256_modulus ->
  (x * 256 + b) mod haskell_word256_modulus = (y * 256 + b) mod haskell_word256_modulus.
Proof.
  intro HE. assert (HM : haskell_word256_modulus <> 0) by
    (pose proof haskell_word256_modulus_positive; lia).
  rewrite (Z.add_mod (x * 256) b _ HM), (Z.add_mod (y * 256) b _ HM).
  rewrite (Z.mul_mod x 256 _ HM), (Z.mul_mod y 256 _ HM), HE. reflexivity.
Qed.

Lemma be_integer_bytes_mod_congruent bytes : forall x y,
  x mod haskell_word256_modulus = y mod haskell_word256_modulus ->
  be_integer_bytes bytes x mod haskell_word256_modulus =
    be_integer_bytes bytes y mod haskell_word256_modulus.
Proof.
  induction bytes as [|b rest IH]; intros x y HE; cbn [be_integer_bytes].
  - exact HE.
  - apply IH. apply haskell_append_byte_mod_congruent. exact HE.
Qed.

Lemma haskell_be256_run_integer bytes : forall z,
  haskell_word256_integer (haskell_be256_run bytes (haskell_word256_from_integer z)) =
    be_integer_bytes bytes z mod haskell_word256_modulus.
Proof.
  induction bytes as [|b rest IH]; intro z; cbn [haskell_be256_run be_integer_bytes].
  - apply haskell_word256_from_integer_unsigned.
  - rewrite haskell_be256_step_append, haskell_word256_from_integer_unsigned, IH.
    apply be_integer_bytes_mod_congruent. apply haskell_append_byte_mod_congruent.
    apply Z.mod_mod. pose proof haskell_word256_modulus_positive; lia.
Qed.

Definition haskell_integer_hash256 bytes :=
  haskell_word256_integer (haskell_be256_run bytes (haskell_word256_from_integer 0)).

Lemma haskell_hash_to_word256_bytes bytes :
  haskell_to_word 8 (haskell_integer_hash256 bytes) =
    haskell_to_word 8 (be_integer_bytes bytes 0).
Proof.
  unfold haskell_integer_hash256. rewrite haskell_be256_run_integer.
  rewrite !haskell_to_word_matches.
  exact (word_fromZ_mod 8 (be_integer_bytes bytes 0)).
Qed.

Lemma be_integer_bytes_append a b z :
  be_integer_bytes (a ++ b) z = be_integer_bytes b (be_integer_bytes a z).
Proof. revert z. induction a; intro z; cbn [app be_integer_bytes]; [reflexivity|apply IHa]. Qed.

Lemma hash_Shr_unsigned i n : 0 <= n < 32 ->
  Int.unsigned (Shr n i) = Int.unsigned i / two_p n.
Proof.
  intros Hn. unfold Shr. rewrite Int.shru_div_two_p.
  rewrite (Int.unsigned_repr n) by (change Int.max_unsigned with 4294967295; lia).
  apply Int.unsigned_repr.
  assert (HD : 1 <= two_p n).
  { change (two_p 0 <= two_p n). apply two_p_monotone. lia. }
  pose proof (Int.unsigned_range i) as Hi.
  split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; [lia|]. change Int.max_unsigned with 4294967295.
  change Int.modulus with 4294967296 in Hi. nia.
Qed.

Lemma be_integer_bytes_word32 i z :
  be_integer_bytes (intlist_to_bytelist [i]) z = z * 4294967296 + Int.unsigned i.
Proof.
  change (((((z * 256 + Byte.unsigned (Byte.repr (Int.unsigned (Shr 24 i)))) * 256 +
    Byte.unsigned (Byte.repr (Int.unsigned (Shr 16 i)))) * 256 +
    Byte.unsigned (Byte.repr (Int.unsigned (Shr 8 i)))) * 256 +
    Byte.unsigned (Byte.repr (Int.unsigned i))) = z * 4294967296 + Int.unsigned i).
  rewrite !Byte.unsigned_repr_eq.
  rewrite (hash_Shr_unsigned i 24 ltac:(lia)), (hash_Shr_unsigned i 16 ltac:(lia)),
    (hash_Shr_unsigned i 8 ltac:(lia)).
  change Byte.modulus with 256.
  change (two_p 24) with 16777216. change (two_p 16) with 65536. change (two_p 8) with 256.
  pose proof (four_limbs_horner_mod 256 (Int.unsigned i) ltac:(lia)) as H.
  rewrite !Z.div_div in H by lia.
  rewrite (Z.mod_small (Int.unsigned i) (256 * 256 * 256 * 256)) in H by exact (Int.unsigned_range i).
  change (256 * 256 * 256) with 16777216 in H.
  change (256 * 256) with 65536 in H.
  nia.
Qed.

Fixpoint be_integer_registers (regs : list int) (z : Z) : Z :=
  match regs with
  | [] => z
  | i :: rest => be_integer_registers rest (z * 4294967296 + Int.unsigned i)
  end.

Lemma be_integer_bytes_registers regs : forall z,
  be_integer_bytes (intlist_to_bytelist regs) z = be_integer_registers regs z.
Proof.
  induction regs as [|i rest IH]; intro z; [reflexivity|].
  change (be_integer_bytes (intlist_to_bytelist [i] ++ intlist_to_bytelist rest) z =
    be_integer_registers rest (z * 4294967296 + Int.unsigned i)).
  rewrite be_integer_bytes_append, be_integer_bytes_word32. apply IH.
Qed.

Lemma from_hash256_integer h :
  @toZ (WordToZ 8) (from_hash256 h) = be_integer_registers (hash256_reg h) 0.
Proof.
  destruct h as [regs Hlen].
  destruct regs as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 regs]]]]]]]]];
    cbn in Hlen; try discriminate.
  set (w := fun i : int => @fromZ (WordToZ 5) (Int.unsigned i)).
  change (@toZ (WordToZ 8)
    (((w a0, w a1), (w a2, w a3)), ((w a4, w a5), (w a6, w a7))) =
    be_integer_registers [a0;a1;a2;a3;a4;a5;a6;a7] 0).
  rewrite (@toZ_Pair (WordToZ 7) (WordToZ 7)).
  rewrite !(@toZ_Pair (WordToZ 6) (WordToZ 6)).
  rewrite !(@toZ_Pair (WordToZ 5) (WordToZ 5)).
  unfold w. rewrite !to_fromZ.
  change (two_power_nat (bitSize (WordToZ 5))) with 4294967296.
  rewrite !Z.mod_small by apply Int.unsigned_range.
  change (two_power_nat (bitSize (WordToZ 6))) with 18446744073709551616.
  change (two_power_nat (bitSize (WordToZ 7))) with 340282366920938463463374607431768211456.
  cbn [be_integer_registers]. ring.
Qed.

Lemma haskell_hash_word256 h :
  haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)) = from_hash256 h.
Proof.
  rewrite haskell_hash_to_word256_bytes. unfold hash256_to_bytelist.
  rewrite be_integer_bytes_registers, <- from_hash256_integer, haskell_to_word_matches.
  apply from_toZ.
Qed.

Lemma haskell_hash_bytes_length h : length (hash256_to_bytelist h) = 32%nat.
Proof.
  unfold hash256_to_bytelist. rewrite length_intlist_to_bytelist, hash256_len. reflexivity.
Qed.

Lemma haskell_word64_modulus_literal : haskell_word64_modulus = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma haskell_word256_modulus_literal : haskell_word256_modulus = 2 ^ 256.
Proof. reflexivity. Qed.

Print Assumptions haskell_word256_from_integer_unsigned.
Print Assumptions haskell_shift_or_byte.
Print Assumptions haskell_append_byte_div.
Print Assumptions haskell_append_byte_mod.
Print Assumptions haskell_word256_or_byte.
Print Assumptions haskell_be256_step_append.
Print Assumptions haskell_be256_run_integer.
Print Assumptions haskell_hash_to_word256_bytes.
Print Assumptions be_integer_bytes_word32.
Print Assumptions haskell_hash_word256.
