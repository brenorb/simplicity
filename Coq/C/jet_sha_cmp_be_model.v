(** The lexicographic comparison of the words of two 256-bit values is the
    comparison of the values. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_word_repr C.jet_forWhile_seq C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_model C.jet_sha_cmp_be_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Fixpoint be_val (ws : list (Ty.tySem (Word 5))) : Z :=
  match ws with
  | [] => 0
  | w :: ws' => @toZ (WordToZ 5) w * 2 ^ (32 * Z.of_nat (length ws')) + be_val ws'
  end.

Lemma be_val_range ws : 0 <= be_val ws < 2 ^ (32 * Z.of_nat (length ws)).
Proof.
  induction ws as [|w ws IH]; [cbn; lia|].
  pose proof (word_toZ_range 5 w) as HW. change (2 ^ Z.of_nat (Nat.pow 2 5)) with (2 ^ 32) in HW.
  cbn [be_val length]. set (M := 2 ^ (32 * Z.of_nat (length ws))) in *.
  assert (HM : 0 < M) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ (32 * Z.of_nat (S (length ws)))) with (2 ^ 32 * M).
  2:{ unfold M. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma be_val_app xs ys :
  be_val (xs ++ ys) = be_val xs * 2 ^ (32 * Z.of_nat (length ys)) + be_val ys.
Proof.
  induction xs as [|x xs IH]; [cbn; lia|].
  cbn [app be_val]. rewrite IH, app_length, Nat2Z.inj_add, Z.mul_add_distr_l, Z.pow_add_r by lia. ring.
Qed.

Lemma be_val_chunks n (x : Ty.tySem (Word (n + 5))) :
  @toZ (WordToZ (n + 5)) x = be_val (word32_chunks n x).
Proof.
  induction n as [|n IH].
  - change (@toZ (WordToZ 5) x = @toZ (WordToZ 5) x * 1 + 0). lia.
  - destruct x as [hi lo].
    change (word32_chunks (S n) (hi, lo)) with (word32_chunks n hi ++ word32_chunks n lo).
    rewrite be_val_app, <- (IH hi), <- (IH lo), word32_chunks_length.
    etransitivity; [exact (wz_pair (n + 5) hi lo)|]. unfold wz, wsize.
    assert (HE : Z.of_nat (Nat.pow 2 (n + 5)) = 32 * Z.of_nat (Nat.pow 2 n))
      by (rewrite Nat.pow_add_r; change (Nat.pow 2 5) with 32%nat; lia).
    rewrite HE. reflexivity.
Qed.

Lemma cmp_model_words : forall xs ys : list (Ty.tySem (Word 5)), length xs = length ys ->
  Int.lt (cmp_model (map word32_array_value xs) (map word32_array_value ys)) Int.zero =
    (be_val xs <? be_val ys).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] HL; try discriminate HL; [reflexivity|].
  cbn [map cmp_model be_val]. injection HL as HL0.
  assert (HL : length xs = length ys) by exact HL0. clear HL0.
  pose proof (word_toZ_range 5 x) as HX. pose proof (word_toZ_range 5 y) as HY.
  change (2 ^ Z.of_nat (Nat.pow 2 5)) with 4294967296 in HX, HY.
  pose proof (be_val_range xs) as RX.
  assert (RY : 0 <= be_val ys < 2 ^ (32 * Z.of_nat (length xs)))
    by (rewrite HL; exact (be_val_range ys)).
  assert (EM : 2 ^ (32 * Z.of_nat (length ys)) = 2 ^ (32 * Z.of_nat (length xs)))
    by (rewrite HL; reflexivity).
  rewrite EM. set (M := 2 ^ (32 * Z.of_nat (length xs))) in *.
  assert (HM : 0 < M) by (apply Z.pow_pos_nonneg; lia).
  unfold word32_array_value.
  set (tx := @toZ (WordToZ 5) x) in *. set (ty := @toZ (WordToZ 5) y) in *.
  assert (UX : Int.unsigned (Int.repr tx) = tx)
    by (apply Int.unsigned_repr; change Int.max_unsigned with 4294967295; lia).
  assert (UY : Int.unsigned (Int.repr ty) = ty)
    by (apply Int.unsigned_repr; change Int.max_unsigned with 4294967295; lia).
  destruct (Z.eq_dec tx ty) as [E|E].
  - rewrite E, Int.eq_true. fold (word32_array_value). 
    change (Int.lt (cmp_model (map word32_array_value xs) (map word32_array_value ys)) Int.zero =
      (ty * M + be_val xs <? ty * M + be_val ys)).
    rewrite (IH ys HL).
    destruct (Z.ltb_spec (be_val xs) (be_val ys)); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
  - rewrite Int.eq_false by (intro HE; apply E; rewrite <- UX, <- UY, HE; reflexivity).
    unfold cmp_res, Int.ltu. rewrite UX, UY.
    destruct (Coqlib.zlt tx ty) as [L|L].
    + change (Int.lt (Int.neg (Int.repr 1)) Int.zero) with true. symmetry. apply Z.ltb_lt. nia.
    + change (Int.lt (Int.repr 1) Int.zero) with false. symmetry. apply Z.ltb_ge. nia.
Qed.

Theorem cmp_model_lt (a b : Ty.tySem (Word 8)) :
  Int.lt (cmp_model (state_regs a) (state_regs b)) Int.zero =
    (@toZ (WordToZ 8) a <? @toZ (WordToZ 8) b).
Proof.
  unfold state_regs. rewrite cmp_model_words by (rewrite !(word32_chunks_length 3); reflexivity).
  rewrite <- (be_val_chunks 3 a), <- (be_val_chunks 3 b). reflexivity.
Qed.
