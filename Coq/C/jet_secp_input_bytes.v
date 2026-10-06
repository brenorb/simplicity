(** Input-byte decoding bridge for the original secp frame reader. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_frame_bits C.jet_secp_fe_math.
Require Import Simplicity.Ty Simplicity.Word C.jet_encoding C.jet_word_repr C.jet_input_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bits_val_app left_bits right_bits :
  bits_val (left_bits ++ right_bits) =
    bits_val left_bits * 2 ^ Z.of_nat (length right_bits) + bits_val right_bits.
Proof.
  induction left_bits as [|bit tail IH]; cbn [app bits_val]; [lia|].
  rewrite app_length, Nat2Z.inj_add, Z.pow_add_r by lia.
  rewrite IH; destruct bit; ring.
Qed.

Lemma fold_be_linear bytes : forall acc,
  fold_left (fun value byte => value * 256 + byte) bytes acc =
    acc * 256 ^ Z.of_nat (length bytes) + be_val bytes.
Proof.
  induction bytes as [|byte tail IH]; intro acc; [cbn [fold_left length be_val]; lia|].
  change (fold_left (fun value byte => value * 256 + byte) tail (acc * 256 + byte) =
    acc * 256 ^ Z.of_nat (S (length tail)) +
    fold_left (fun value byte => value * 256 + byte) tail byte).
  rewrite (IH (acc * 256 + byte)), (IH byte), Nat2Z.inj_succ, Z.pow_succ_r by lia.
  ring.
Qed.

Lemma be_val_cons byte bytes :
  be_val (byte :: bytes) = byte * 256 ^ Z.of_nat (length bytes) + be_val bytes.
Proof.
  change (fold_left (fun value byte => value * 256 + byte) bytes byte =
    byte * 256 ^ Z.of_nat (length bytes) + be_val bytes).
  apply fold_be_linear.
Qed.

Fixpoint input_bytes (count : nat) (bits : list bool) : list Z :=
  match count with
  | 0%nat => []
  | S n => bits_val (firstn 8 bits) :: input_bytes n (skipn 8 bits)
  end.
Lemma input_bytes_length count bits : length (input_bytes count bits) = count.
Proof. revert bits; induction count; intros bits; cbn; congruence. Qed.

Lemma input_bytes_value count : forall bits,
  length bits = (8 * count)%nat -> be_val (input_bytes count bits) = bits_val bits.
Proof.
  induction count as [|count IH]; intros bits HLength.
  - destruct bits; [reflexivity|discriminate].
  - cbn [input_bytes]; rewrite be_val_cons, input_bytes_length.
    assert (HTail : length (skipn 8 bits) = (8 * count)%nat).
    { rewrite skipn_length, HLength; lia. }
    rewrite (IH _ HTail).
    pose proof (bits_val_app (firstn 8 bits) (skipn 8 bits)) as HSplit.
    rewrite firstn_skipn, HTail in HSplit.
    rewrite HSplit.
    replace (2 ^ Z.of_nat (8 * count)) with (256 ^ Z.of_nat count).
    + reflexivity.
    + rewrite Nat2Z.inj_mul, Z.pow_mul_r by lia; reflexivity.
Qed.

Lemma input_bytes_nth count : forall bits j,
  (j < count)%nat ->
  nth_error (input_bytes count bits) j = Some (ifield bits (8 * j) 8).
Proof.
  induction count as [|count IH]; intros bits j HIndex; [lia|].
  destruct j as [|j].
  - reflexivity.
  - cbn [input_bytes nth_error]; rewrite (IH _ j ltac:(lia)).
    unfold ifield; rewrite skipn_skipn.
    replace (8 * S j)%nat with (8 * j + 8)%nat by lia; reflexivity.
Qed.

Lemma input_bytes_bounds count bits :
  length bits = (8 * count)%nat ->
  Forall (fun byte => 0 <= byte <= 255) (input_bytes count bits).
Proof.
  intro HLength; apply Forall_forall; intros byte HIn.
  apply In_nth_error in HIn; destruct HIn as [j HNth].
  assert (HIndex : (j < count)%nat).
  { rewrite <- (input_bytes_length count bits); apply nth_error_Some; congruence. }
  rewrite (input_bytes_nth count bits j HIndex) in HNth; inversion HNth; subst byte.
  pose proof (ifield_range bits (8 * j) 8 ltac:(rewrite HLength; lia)) as HRange.
  change (2 ^ Z.of_nat 8) with 256 in HRange.
  change (0 <= ifield bits (8 * j) 8 <= 255); lia.
Qed.


Lemma bits_val_canonical_word n : forall (value : Ty.tySem (Word n)),
  bits_val (frame_input_word_bits value) = @toZ (WordToZ n) value.
Proof.
  induction n as [|n IH]; intro value.
  - destruct value as [[]|[]]; reflexivity.
  - destruct value as [hi lo].
    rewrite frame_input_word_bits_msb.
    assert (HValue : @toZ (WordToZ (S n)) (hi, lo) =
      @toZ (WordToZ n) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo) by exact (@toZ_Pair (WordToZ n) (WordToZ n) hi lo).
    rewrite HValue, two_power_nat_equiv, word_bitSize.
    replace (Nat.pow 2 (S n)) with (Nat.pow 2 n + Nat.pow 2 n)%nat by (cbn; lia).
    rewrite msb_bits_app by apply word_toZ_range.
    rewrite bits_val_app, <- !frame_input_word_bits_msb, frame_input_word_bits_length.
    rewrite (IH hi), (IH lo); reflexivity.
Qed.

Theorem input_bytes_word256_value (value : Ty.tySem (Word 8)) :
  be_val (input_bytes 32 (frame_input_word_bits value)) = @toZ (WordToZ 8) value.
Proof.
  rewrite input_bytes_value.
  - apply bits_val_canonical_word.
  - rewrite frame_input_word_bits_length; reflexivity.
Qed.

Lemma input_bytes_word256_bounds (value : Ty.tySem (Word 8)) :
  Forall (fun byte => 0 <= byte <= 255) (input_bytes 32 (frame_input_word_bits value)).
Proof. apply input_bytes_bounds; rewrite frame_input_word_bits_length; reflexivity. Qed.

Lemma ifield_byte_bounds bits offset : 0 <= ifield bits offset 8 <= 255.
Proof.
  unfold ifield; pose proof (bits_val_range (firstn 8 (skipn offset bits))) as HRange.
  assert (HLength : (length (firstn 8 (skipn offset bits)) <= 8)%nat).
  { rewrite firstn_length; apply Nat.le_min_l. }
  assert (HPow : 2 ^ Z.of_nat (length (firstn 8 (skipn offset bits))) <= 2 ^ 8).
  { apply Z.pow_le_mono_r; lia. }
  change (2 ^ 8) with 256 in HPow; lia.
Qed.

Lemma input_bytes_nth_total count bits j :
  length bits = (8 * count)%nat ->
  nth j (input_bytes count bits) 0 = ifield bits (8 * j) 8.
Proof.
  intro HLength; destruct (Nat.lt_ge_cases j count) as [HIndex|HIndex].
  - pose proof (input_bytes_nth count bits j HIndex) as HNth.
    apply nth_error_nth with (d := 0) in HNth; exact HNth.
  - rewrite nth_overflow by (rewrite input_bytes_length; exact HIndex).
    unfold ifield; rewrite skipn_all2 by (rewrite HLength; lia); reflexivity.
Qed.
