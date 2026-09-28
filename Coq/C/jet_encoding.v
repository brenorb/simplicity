(** Canonical Simplicity encodings of the memory observations used by the
    public jet theorems.

    Every statement in this module concerns memory contents only; no C reader
    or writer is executed.  A read frame is observed most significant cell
    first, starting from [edge - 1] (see [C/frame.h]); a write frame stores the
    cell written [i] steps after the cursor at offset [cursor - 1 - i].  The
    results below relate those algorithm-independent observations, and the
    older extraction-based observations used by the public theorems, to
    [Translate.encode], the cell encoding used by the Bit Machine translation
    of Simplicity. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_word_repr C.jet_frame_spec C.jet_frame_arith C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_crossing_word C.jet_read8_layout_total C.jet_spec.
Require Import C.jet_write_layout C.jet_output_layout C.jet_word_slice C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_carry_wide_layout C.jet_carry_byte_layout.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

(** * Words and their cell encodings *)

(** The [N] low bits of [z], most significant first. *)
Definition msb_bits (N : nat) (z : Z) : list bool :=
  map (fun i => Z.testbit z (Z.of_nat (N - S i))) (List.seq 0 N).

Lemma map_seq_add {A} (f : nat -> A) start N M :
  map f (List.seq (start + N) M) = map (fun i => f (N + i)%nat) (List.seq start M).
Proof.
  revert start. induction M as [|M IH]; intros start; [reflexivity|].
  cbn [List.seq map]. f_equal; [f_equal; lia|].
  replace (S (start + N)) with (S start + N)%nat by lia. apply IH.
Qed.

Lemma msb_bits_app N M hi lo :
  0 <= lo < 2 ^ Z.of_nat M ->
  msb_bits (N + M) (hi * 2 ^ Z.of_nat M + lo) = msb_bits N hi ++ msb_bits M lo.
Proof.
  intros Hlo. unfold msb_bits. rewrite seq_app, map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi.
    replace (Z.of_nat (N + M - S i)) with (Z.of_nat (N - S i) + Z.of_nat M) by lia.
    rewrite <- Z.div_pow2_bits by lia. f_equal.
    rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
    rewrite Z.div_small by exact Hlo. lia.
  - rewrite (map_seq_add _ 0 N M). apply map_ext_in. intros i Hi. apply in_seq in Hi.
    replace (N + M - S (N + i))%nat with (M - S i)%nat by lia.
    rewrite <- (Z.mod_pow2_bits_low _ (Z.of_nat M)) by lia.
    rewrite (Z.add_comm (hi * _)), Z_mod_plus_full, Z.mod_small by exact Hlo.
    reflexivity.
Qed.

Lemma frame_input_word_bits_msb n (x : Ty.tySem (Word n)) :
  frame_input_word_bits x = msb_bits (Nat.pow 2 n) (@toZ (WordToZ n) x).
Proof. reflexivity. Qed.

(** The Bit Machine encoding of a word is its sequence of bits, most
    significant first, which is exactly [frame_input_word_bits]. *)
Theorem encode_word n (x : Ty.tySem (Word n)) :
  encode x = map Some (frame_input_word_bits x).
Proof.
  rewrite frame_input_word_bits_msb. revert x. induction n as [|n IH]; intros x.
  - destruct x as [[]|[]]; reflexivity.
  - destruct x as [hi lo].
    change (@encode (Word (S n)) (hi, lo)) with
      (@encode (Word n) hi ++ @encode (Word n) lo).
    rewrite (IH hi), (IH lo), <- map_app. f_equal.
    symmetry.
    assert (Hp : @toZ (WordToZ (S n)) (hi, lo) =
      @toZ (WordToZ n) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo) by exact (@toZ_Pair (WordToZ n) (WordToZ n) hi lo).
    rewrite Hp, two_power_nat_equiv, word_bitSize.
    replace (Nat.pow 2 (S n)) with (Nat.pow 2 n + Nat.pow 2 n)%nat by (cbn; lia).
    apply msb_bits_app. apply word_toZ_range.
Qed.

Lemma encode_word_length n (x : Ty.tySem (Word n)) :
  length (encode x) = Nat.pow 2 n.
Proof. rewrite encode_word, map_length. apply frame_input_word_bits_length. Qed.

Lemma nth_error_word_bits n (x : Ty.tySem (Word n)) i :
  (i < Nat.pow 2 n)%nat ->
  nth_error (frame_input_word_bits x) i =
    Some (Z.testbit (@toZ (WordToZ n) x) (Z.of_nat (Nat.pow 2 n) - 1 - Z.of_nat i)).
Proof.
  intros Hi. unfold frame_input_word_bits. rewrite nth_error_map.
  rewrite nth_error_seq_in by exact Hi. cbn. do 2 f_equal. lia.
Qed.

(** * Cells *)

(** A physical bit represents a cell when the cell is defined and equal to it,
    or when the cell is undefined (padding) and the bit exists. *)
Definition cell_matches (P : bool -> Prop) (c : Cell) : Prop :=
  match c with Some b => P b | None => exists b, P b end.

Lemma nth_error_app_split {A} (xs ys : list A) i (c : A) :
  nth_error (xs ++ ys) i = Some c <->
  ((i < length xs)%nat /\ nth_error xs i = Some c) \/
  ((length xs <= i)%nat /\ nth_error ys (i - length xs) = Some c).
Proof.
  destruct (Nat.lt_ge_cases i (length xs)) as [Hl|Hg].
  - rewrite nth_error_app1 by exact Hl. split; [intros H; left; auto|].
    intros [[_ H]|[H _]]; [exact H|lia].
  - rewrite nth_error_app2 by exact Hg. split; [intros H; right; auto|].
    intros [[H _]|[_ H]]; [lia|exact H].
Qed.

(** ** Read frames *)

Definition frame_input_cells_at (m : mem) (bw : block) (edge cursor : Z)
    (cells : list Cell) : Prop :=
  forall i c, nth_error cells i = Some c ->
    cell_matches (frame_input_bit_at m bw edge (cursor + Z.of_nat i)) c.

Lemma frame_input_cells_at_app m bw edge cursor xs ys :
  frame_input_cells_at m bw edge cursor (xs ++ ys) <->
  frame_input_cells_at m bw edge cursor xs /\
  frame_input_cells_at m bw edge (cursor + Z.of_nat (length xs)) ys.
Proof.
  unfold frame_input_cells_at. split.
  - intros H. split.
    + intros i c Hi. apply H. apply nth_error_app_split. left. split; [|exact Hi].
      apply nth_error_Some. rewrite Hi. discriminate.
    + intros i c Hi.
      replace (cursor + Z.of_nat (length xs) + Z.of_nat i)
        with (cursor + Z.of_nat (length xs + i)) by lia.
      apply H. apply nth_error_app_split. right. split; [lia|].
      replace (length xs + i - length xs)%nat with i by lia. exact Hi.
  - intros [HX HY] i c Hi. apply nth_error_app_split in Hi.
    destruct Hi as [[_ Hi]|[Hg Hi]]; [exact (HX _ _ Hi)|].
    specialize (HY _ _ Hi).
    replace (cursor + Z.of_nat i) with
      (cursor + Z.of_nat (length xs) + Z.of_nat (i - length xs)) by lia.
    exact HY.
Qed.

Lemma frame_input_cells_at_bits m bw edge cursor bits :
  frame_input_cells_at m bw edge cursor (map Some bits) <->
  frame_input_bits_at m bw edge cursor bits.
Proof.
  unfold frame_input_cells_at, frame_input_bits_at. split.
  - intros H i b Hi. apply (H i (Some b)). rewrite nth_error_map, Hi. reflexivity.
  - intros H i c Hi. rewrite nth_error_map in Hi.
    destruct (nth_error bits i) eqn:E; [|discriminate].
    injection Hi as <-. exact (H _ _ E).
Qed.

(** The wide input contract used by the 16/32/64-bit theorems is exactly the
    statement that the input cells hold [encode x]. *)
Theorem frame_input_word_at_encode {n} m bw edge cursor (x : Ty.tySem (Word n)) :
  frame_input_word_at m bw edge cursor x <->
  frame_input_cells_at m bw edge cursor (encode x).
Proof.
  rewrite encode_word, frame_input_cells_at_bits. reflexivity.
Qed.

Theorem frame_input_word_pair_encode {n} m bw edge cursor (x y : Ty.tySem (Word n)) :
  frame_input_word_at m bw edge cursor x /\
  frame_input_word_at m bw edge (cursor + Z.of_nat (Nat.pow 2 n)) y <->
  frame_input_cells_at m bw edge cursor (@encode (Ty.Prod (Word n) (Word n)) (x, y)).
Proof.
  change (@encode (Ty.Prod (Word n) (Word n)) (x, y)) with (encode x ++ encode y).
  rewrite frame_input_cells_at_app, encode_word_length,
    <- !frame_input_word_at_encode.
  reflexivity.
Qed.

Lemma frame_input_word_at_iff {n} m bw edge cursor (x : Ty.tySem (Word n)) :
  frame_input_word_at m bw edge cursor x <->
  forall i, 0 <= i < Z.of_nat (Nat.pow 2 n) ->
    frame_input_bit_at m bw edge (cursor + i)
      (Z.testbit (@toZ (WordToZ n) x) (Z.of_nat (Nat.pow 2 n) - 1 - i)).
Proof.
  unfold frame_input_word_at, frame_input_bits_at. split.
  - intros H i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    apply H. rewrite nth_error_word_bits by lia. reflexivity.
  - intros H i b Hi.
    assert (Hlt : (i < Nat.pow 2 n)%nat).
    { rewrite <- (frame_input_word_bits_length x). apply nth_error_Some.
      rewrite Hi. discriminate. }
    rewrite nth_error_word_bits in Hi by exact Hlt. injection Hi as <-.
    apply H. lia.
Qed.

Lemma frame_input_bit_word m bw edge q b w :
  frame_input_bit_at m bw edge q b ->
  Mem.load Mint64 m bw (edge - 8 * (1 + q / 64)) = Some (Vlong w) ->
  b = Int64.testbit w (63 - q mod 64).
Proof.
  intros [_ [_ [w' [HL' Hb]]]] HL. rewrite HL in HL'.
  injection HL' as <-. exact Hb.
Qed.

Lemma div_mod_64 q t r :
  0 <= r < 64 -> q = 64 * t + r -> q / 64 = t /\ q mod 64 = r.
Proof.
  intros Hr Hq. split.
  - symmetry. apply (Z.div_unique q 64 t r); [left; lia|lia].
  - symmetry. apply (Z.mod_unique q 64 t r); [left; lia|lia].
Qed.

(** Bits of the legacy byte extraction, stated in frame positions. *)
Lemma read8_layout_byte_bits cursor high low j :
  0 <= cursor -> 0 <= j < 8 ->
  Int64.testbit (read8_layout_byte cursor high low) j =
    if zlt (cursor mod 64 + (7 - j)) 64
    then Int64.testbit high (63 - (cursor mod 64 + (7 - j)))
    else Int64.testbit low (127 - (cursor mod 64 + (7 - j))).
Proof.
  intros HC HJ.
  assert (HJ64 : 0 <= j < Int64.zwordsize) by (change Int64.zwordsize with 64; lia).
  unfold read8_layout_byte.
  assert (Hr : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  set (r := cursor mod 64) in *.
  destruct (Z_le_dec r 56) as [HN|HX].
  - rewrite zlt_true by lia. rewrite Int64.bits_shru by exact HJ64.
    rewrite cursor_unsigned by lia. change Int64.zwordsize with 64.
    rewrite zlt_true by lia. f_equal; lia.
  - unfold crossing_byte.
    rewrite Int64.bits_or, Int64.bits_shl, Int64.bits_shru by exact HJ64.
    rewrite !cursor_unsigned by lia. change Int64.zwordsize with 64.
    destruct (zlt j (8 - (64 - r))) as [HL|HH].
    + rewrite zlt_true by lia. rewrite zlt_false by lia. cbn [orb]. f_equal; lia.
    + rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
      rewrite zlt_false by lia. rewrite zlt_true by lia.
      rewrite orb_false_r. f_equal; lia.
Qed.

(** The legacy byte slice used by the 8-bit arithmetic theorems observes
    exactly the encoded input cells, plus a representable final cursor. *)
Theorem byte_slice_at_encode m bw edge cursor (x : Ty.tySem Word8) :
  byte_slice_at m bw edge cursor x <->
  0 <= cursor <= Int64.max_unsigned - 8 /\
  frame_input_cells_at m bw edge cursor (encode x).
Proof.
  rewrite <- frame_input_word_at_encode, frame_input_word_at_iff.
  change (Z.of_nat (Nat.pow 2 3)) with 8.
  assert (Hdiv := fun c => Z.div_mod c 64 ltac:(lia)).
  split.
  - intros [Hcur [Hedge [high [low [HH [HL Hdec]]]]]]. split; [exact Hcur|].
    unfold decode_word8 in Hdec. pose proof (proj1 (word_fromZ_bits 3 x _) Hdec) as Hdec0.
    clear Hdec. rename Hdec0 into Hdec.
    change (Z.of_nat (Nat.pow 2 3)) with 8 in Hdec.
    intros i Hi.
    assert (Hr : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    pose proof (Hdec (7 - i) ltac:(lia)) as Hbit.
    change (Z.testbit (Int64.unsigned (read8_layout_byte cursor high low)) (7 - i))
      with (Int64.testbit (read8_layout_byte cursor high low) (7 - i)) in Hbit.
    rewrite read8_layout_byte_bits in Hbit by lia.
    replace (7 - (7 - i)) with i in Hbit by lia.
    replace (8 - 1 - i) with (7 - i) by lia.
    split; [lia|].
    destruct (zlt (cursor mod 64 + i) 64) as [HN|HX].
    + destruct (div_mod_64 (cursor + i) (cursor / 64) (cursor mod 64 + i))
        as [Hq Hm]; [lia|specialize (Hdiv cursor); lia|].
      rewrite Hq, Hm. split; [lia|]. exists high. split; [exact HH|].
      rewrite <- Hbit. reflexivity.
    + assert (H56 : 56 < cursor mod 64) by lia.
      destruct (HL H56) as [Hedge2 HL2].
      destruct (div_mod_64 (cursor + i) (cursor / 64 + 1) (cursor mod 64 + i - 64))
        as [Hq Hm]; [lia|specialize (Hdiv cursor); lia|].
      rewrite Hq, Hm. split; [lia|]. exists low. split.
      * replace (edge - 8 * (1 + (cursor / 64 + 1))) with
          (edge - 8 * (2 + cursor / 64)) by lia. exact HL2.
      * rewrite <- Hbit. unfold Int64.testbit. f_equal. lia.
  - intros [Hcur Hbits].
    assert (Hr : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    pose proof (Hbits 0 ltac:(lia)) as H0.
    rewrite Z.add_0_r in H0.
    destruct H0 as [_ [Hedge0 [high [HH _]]]].
    assert (Hhigh : forall i, 0 <= i < 8 -> cursor mod 64 + i < 64 ->
      Z.testbit (@toZ (WordToZ 3) x) (8 - 1 - i) =
        Int64.testbit high (63 - (cursor mod 64 + i))).
    { intros i Hi HN. pose proof (Hbits i Hi) as Hb.
      destruct (div_mod_64 (cursor + i) (cursor / 64) (cursor mod 64 + i))
        as [Hq Hm]; [lia|specialize (Hdiv cursor); lia|].
      rewrite (frame_input_bit_word _ _ _ _ _ high Hb) by (rewrite Hq; exact HH).
      rewrite Hm. reflexivity. }
    split; [exact Hcur|]. split; [exact Hedge0|].
    destruct (Z_le_dec (cursor mod 64) 56) as [HN|HX].
    + exists high, Int64.zero. split; [exact HH|]. split; [lia|].
      unfold decode_word8. apply (proj2 (word_fromZ_bits 3 x _)).
      change (Z.of_nat (Nat.pow 2 3)) with 8. intros j Hj.
      change (Z.testbit (Int64.unsigned (read8_layout_byte cursor high Int64.zero)) j)
        with (Int64.testbit (read8_layout_byte cursor high Int64.zero) j).
      rewrite read8_layout_byte_bits by lia. rewrite zlt_true by lia.
      rewrite <- Hhigh by lia. f_equal. lia.
    + pose proof (Hbits 7 ltac:(lia)) as H7.
      destruct (div_mod_64 (cursor + 7) (cursor / 64 + 1) (cursor mod 64 + 7 - 64))
        as [Hq7 Hm7]; [lia|specialize (Hdiv cursor); lia|].
      destruct H7 as [_ [Hedge7 [low [HL _]]]].
      rewrite Hq7 in Hedge7, HL.
      replace (edge - 8 * (1 + (cursor / 64 + 1))) with
        (edge - 8 * (2 + cursor / 64)) in HL by lia.
      exists high, low. split; [exact HH|]. split; [intros _; split; [lia|exact HL]|].
      unfold decode_word8. apply (proj2 (word_fromZ_bits 3 x _)).
      change (Z.of_nat (Nat.pow 2 3)) with 8. intros j Hj.
      change (Z.testbit (Int64.unsigned (read8_layout_byte cursor high low)) j)
        with (Int64.testbit (read8_layout_byte cursor high low) j).
      rewrite read8_layout_byte_bits by lia.
      destruct (zlt (cursor mod 64 + (7 - j)) 64) as [HN|HC].
      * rewrite <- Hhigh by lia. f_equal. lia.
      * pose proof (Hbits (7 - j) ltac:(lia)) as Hb.
        destruct (div_mod_64 (cursor + (7 - j)) (cursor / 64 + 1)
          (cursor mod 64 + (7 - j) - 64)) as [Hq Hm]; [lia|specialize (Hdiv cursor); lia|].
        assert (HLq : Mem.load Mint64 m bw (edge - 8 * (1 + (cursor + (7 - j)) / 64)) =
          Some (Vlong low)).
        { rewrite Hq. replace (edge - 8 * (1 + (cursor / 64 + 1))) with
            (edge - 8 * (2 + cursor / 64)) by lia. exact HL. }
        pose proof (frame_input_bit_word _ _ _ _ _ low Hb HLq) as Hw.
        replace (8 - 1 - (7 - j)) with j in Hw by lia.
        rewrite Hw, Hm. unfold Int64.testbit. f_equal. lia.
Qed.

Theorem byte_input_single_encode m bf base bw edge cursor (x : Ty.tySem Word8) :
  byte_input_at m bf base bw edge cursor [x] <->
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  0 <= cursor <= Int64.max_unsigned - 8 /\
  frame_input_cells_at m bw edge cursor (encode x).
Proof.
  unfold byte_input_at. split.
  - intros [HB [HF Hs]]. specialize (Hs 0%nat x eq_refl).
    replace (cursor + 8 * Z.of_nat 0) with cursor in Hs by lia.
    apply byte_slice_at_encode in Hs. destruct Hs as [HC HX]. auto.
  - intros [HB [HF [HC HX]]]. split; [exact HB|]. split; [exact HF|].
    intros [|[|i]] x0 Hi; cbn in Hi; try discriminate.
    injection Hi as <-. replace (cursor + 8 * Z.of_nat 0) with cursor by lia.
    apply byte_slice_at_encode. auto.
Qed.

Theorem byte_input_pair_encode m bf base bw edge cursor (x y : Ty.tySem Word8) :
  byte_input_at m bf base bw edge cursor [x; y] <->
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  0 <= cursor <= Int64.max_unsigned - 16 /\
  frame_input_cells_at m bw edge cursor (@encode (Ty.Prod Word8 Word8) (x, y)).
Proof.
  change (@encode (Ty.Prod Word8 Word8) (x, y)) with (encode x ++ encode y).
  rewrite frame_input_cells_at_app, encode_word_length.
  change (Z.of_nat (Nat.pow 2 3)) with 8.
  unfold byte_input_at. split.
  - intros [HB [HF Hs]].
    pose proof (Hs 0%nat x eq_refl) as Hx. pose proof (Hs 1%nat y eq_refl) as Hy.
    replace (cursor + 8 * Z.of_nat 0) with cursor in Hx by lia.
    replace (cursor + 8 * Z.of_nat 1) with (cursor + 8) in Hy by lia.
    apply byte_slice_at_encode in Hx. apply byte_slice_at_encode in Hy.
    destruct Hx as [HCx HX]. destruct Hy as [HCy HY].
    split; [exact HB|]. split; [exact HF|]. split; [lia|]. auto.
  - intros [HB [HF [HC [HX HY]]]]. split; [exact HB|]. split; [exact HF|].
    intros [|[|[|i]]] x0 Hi; cbn in Hi; try discriminate; injection Hi as <-.
    + replace (cursor + 8 * Z.of_nat 0) with cursor by lia.
      apply byte_slice_at_encode. split; [lia|exact HX].
    + replace (cursor + 8 * Z.of_nat 1) with (cursor + 8) by lia.
      apply byte_slice_at_encode. split; [lia|exact HY].
Qed.

(** ** Write frames *)

(** Output cell [q] is the absolute write offset: bit [q mod 64] of the
    backing word [edge + 8 * (q / 64)]. *)
Definition frame_output_bit_at (m : mem) (bw : block) (edge q : Z) (b : bool) : Prop :=
  0 <= q /\ exists w,
    Mem.load Mint64 m bw (edge + 8 * (q / 64)) = Some (Vlong w) /\
    b = Int64.testbit w (q mod 64).

(** Forward cell [i] written from a cursor at offset [cursor] lives at
    offset [cursor - 1 - i]. *)
Definition frame_output_cells_at (m : mem) (bw : block) (edge cursor : Z)
    (cells : list Cell) : Prop :=
  forall i c, nth_error cells i = Some c ->
    cell_matches (frame_output_bit_at m bw edge (cursor - 1 - Z.of_nat i)) c.

Lemma frame_output_cells_at_app m bw edge cursor xs ys :
  frame_output_cells_at m bw edge cursor (xs ++ ys) <->
  frame_output_cells_at m bw edge cursor xs /\
  frame_output_cells_at m bw edge (cursor - Z.of_nat (length xs)) ys.
Proof.
  unfold frame_output_cells_at. split.
  - intros H. split.
    + intros i c Hi. apply H. apply nth_error_app_split. left. split; [|exact Hi].
      apply nth_error_Some. rewrite Hi. discriminate.
    + intros i c Hi.
      replace (cursor - Z.of_nat (length xs) - 1 - Z.of_nat i)
        with (cursor - 1 - Z.of_nat (length xs + i)) by lia.
      apply H. apply nth_error_app_split. right. split; [lia|].
      replace (length xs + i - length xs)%nat with i by lia. exact Hi.
  - intros [HX HY] i c Hi. apply nth_error_app_split in Hi.
    destruct Hi as [[_ Hi]|[Hg Hi]]; [exact (HX _ _ Hi)|].
    specialize (HY _ _ Hi).
    replace (cursor - 1 - Z.of_nat i) with
      (cursor - Z.of_nat (length xs) - 1 - Z.of_nat (i - length xs)) by lia.
    exact HY.
Qed.

Lemma frame_output_bit_word m bw edge q b w :
  frame_output_bit_at m bw edge q b ->
  Mem.load Mint64 m bw (edge + 8 * (q / 64)) = Some (Vlong w) ->
  b = Int64.testbit w (q mod 64).
Proof.
  intros [_ [w' [HL' Hb]]] HL. rewrite HL in HL'. injection HL' as <-. exact Hb.
Qed.

Lemma frame_output_word_iff {n} m bw edge cursor (x : Ty.tySem (Word n)) :
  frame_output_cells_at m bw edge cursor (encode x) <->
  forall j, 0 <= j < Z.of_nat (Nat.pow 2 n) ->
    frame_output_bit_at m bw edge (cursor - Z.of_nat (Nat.pow 2 n) + j)
      (Z.testbit (@toZ (WordToZ n) x) j).
Proof.
  rewrite encode_word. unfold frame_output_cells_at. split.
  - intros H j Hj.
    set (i := Z.to_nat (Z.of_nat (Nat.pow 2 n) - 1 - j)).
    assert (Hi : (i < Nat.pow 2 n)%nat) by (unfold i; lia).
    specialize (H i (Some (Z.testbit (@toZ (WordToZ n) x) j))).
    replace (cursor - Z.of_nat (Nat.pow 2 n) + j) with (cursor - 1 - Z.of_nat i)
      by (unfold i; lia).
    apply H. rewrite nth_error_map, nth_error_word_bits by exact Hi.
    cbn. do 3 f_equal. unfold i. lia.
  - intros H i c Hi. rewrite nth_error_map in Hi.
    assert (Hlt : (i < Nat.pow 2 n)%nat).
    { rewrite <- (frame_input_word_bits_length x). apply nth_error_Some.
      destruct (nth_error (frame_input_word_bits x) i); [discriminate|discriminate Hi]. }
    rewrite nth_error_word_bits in Hi by exact Hlt. injection Hi as <-.
    cbn [cell_matches].
    replace (cursor - 1 - Z.of_nat i) with
      (cursor - Z.of_nat (Nat.pow 2 n) + (Z.of_nat (Nat.pow 2 n) - 1 - Z.of_nat i)) by lia.
    apply H. lia.
Qed.

Lemma crossing_slice_bits n k high low j :
  1 <= k < n -> n <= 64 -> 0 <= j < 64 ->
  Int64.testbit (crossing_slice n k high low) j =
    if zlt j (n - k) then Int64.testbit low (j + (64 - (n - k)))
    else if zlt j n then Int64.testbit high (j - (n - k)) else false.
Proof.
  intros HK HN HJ.
  assert (HJ64 : 0 <= j < Int64.zwordsize) by (change Int64.zwordsize with 64; lia).
  unfold crossing_slice.
  rewrite Int64.bits_or, Int64.bits_shl, Int64.bits_shru by exact HJ64.
  rewrite !cursor_unsigned by lia. change Int64.zwordsize with 64.
  destruct (zlt j (n - k)) as [HL|HH].
  - rewrite zlt_true by lia. reflexivity.
  - rewrite Int64.bits_zero_ext by lia.
    rewrite (zlt_false _ (j + (64 - (n - k))) 64) by lia. rewrite orb_false_r.
    destruct (zlt j n); [rewrite zlt_true by lia|rewrite zlt_false by lia]; reflexivity.
Qed.

(** The extracted payload of [slice_output_at] is the value whose bit [j] is
    output cell [cursor - n + j]. *)
Lemma slice_output_at_bits n m bw edge cursor x :
  1 <= n <= 64 -> n <= cursor ->
  slice_output_at n m bw edge cursor x ->
  forall j, 0 <= j < n ->
    frame_output_bit_at m bw edge (cursor - n + j) (Int64.testbit x j).
Proof.
  intros HN HC. unfold slice_output_at, write_word_address, write_word_shift.
  assert (Hd := Z.div_mod (cursor - 1) 64 ltac:(lia)).
  assert (Hs : 0 <= (cursor - 1) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  set (t := (cursor - 1) / 64) in *. set (s := (cursor - 1) mod 64) in *.
  destruct (Z_le_dec n (1 + s)) as [HNC|HCR].
  - intros [w [HW <-]] j Hj.
    destruct (div_mod_64 (cursor - n + j) t (s + 1 - n + j)) as [Hq Hm]; [lia|lia|].
    split; [lia|]. exists w. rewrite Hq, Hm. split; [exact HW|].
    assert (HJ64 : 0 <= j < Int64.zwordsize) by (change Int64.zwordsize with 64; lia).
    rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia.
    rewrite Int64.bits_shru by exact HJ64. rewrite cursor_unsigned by lia.
    change Int64.zwordsize with 64. rewrite zlt_true by lia. f_equal. lia.
  - intros [high [low [HH [HL <-]]]] j Hj.
    rewrite crossing_slice_bits by lia. split; [lia|].
    destruct (zlt j (n - (1 + s))) as [HLow|HHigh].
    + destruct (div_mod_64 (cursor - n + j) (t - 1) (64 + s + 1 - n + j))
        as [Hq Hm]; [lia|lia|].
      exists low. rewrite Hq, Hm. split.
      * replace (edge + 8 * (t - 1)) with (edge + 8 * t - 8) by lia. exact HL.
      * f_equal. lia.
    + destruct (div_mod_64 (cursor - n + j) t (s + 1 - n + j)) as [Hq Hm]; [lia|lia|].
      exists high. rewrite Hq, Hm. split; [exact HH|].
      rewrite zlt_true by lia. f_equal. lia.
Qed.

Lemma slice_output_at_of_bits n m bw edge cursor v :
  1 <= n <= 64 -> n <= cursor ->
  (forall j, 0 <= j < n ->
    frame_output_bit_at m bw edge (cursor - n + j) (Int64.testbit v j)) ->
  slice_output_at n m bw edge cursor (Int64.zero_ext n v).
Proof.
  intros HN HC Hbits. unfold slice_output_at, write_word_address, write_word_shift.
  assert (Hd := Z.div_mod (cursor - 1) 64 ltac:(lia)).
  assert (Hs : 0 <= (cursor - 1) mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  set (t := (cursor - 1) / 64) in *. set (s := (cursor - 1) mod 64) in *.
  assert (Hhigh : forall j, 0 <= j < n -> n - (1 + s) <= j ->
    (cursor - n + j) / 64 = t /\ (cursor - n + j) mod 64 = s + 1 - n + j).
  { intros j Hj HJ. apply div_mod_64; lia. }
  destruct (Hbits (n - 1) ltac:(lia)) as [_ [w [HW _]]].
  destruct (Hhigh (n - 1) ltac:(lia) ltac:(lia)) as [Hq1 _].
  rewrite Hq1 in HW.
  destruct (Z_le_dec n (1 + s)) as [HNC|HCR].
  - exists w. split; [exact HW|].
    apply Int64.same_bits_eq. intros i Hi. change Int64.zwordsize with 64 in Hi.
    rewrite !Int64.bits_zero_ext by lia. destruct (zlt i n) as [Hin|]; [|reflexivity].
    rewrite Int64.bits_shru by (change Int64.zwordsize with 64; lia).
    rewrite cursor_unsigned by lia. change Int64.zwordsize with 64.
    rewrite zlt_true by lia.
    destruct (Hhigh i ltac:(lia) ltac:(lia)) as [Hq Hm].
    rewrite (frame_output_bit_word _ _ _ _ _ w (Hbits i ltac:(lia))) by (rewrite Hq; exact HW).
    rewrite Hm. f_equal. lia.
  - destruct (Hbits 0 ltac:(lia)) as [_ [low [HL _]]].
    destruct (div_mod_64 (cursor - n + 0) (t - 1) (64 + s + 1 - n)) as [Hq0 _];
      [lia|lia|].
    rewrite Hq0 in HL. replace (edge + 8 * (t - 1)) with (edge + 8 * t - 8) in HL by lia.
    exists w, low. split; [exact HW|]. split; [exact HL|].
    apply Int64.same_bits_eq. intros i Hi. change Int64.zwordsize with 64 in Hi.
    rewrite crossing_slice_bits by lia. rewrite Int64.bits_zero_ext by lia.
    destruct (zlt i (n - (1 + s))) as [HLow|HHigh].
    + rewrite zlt_true by lia.
      destruct (div_mod_64 (cursor - n + i) (t - 1) (64 + s + 1 - n + i))
        as [Hq Hm]; [lia|lia|].
      rewrite (frame_output_bit_word _ _ _ _ _ low (Hbits i ltac:(lia))).
      * rewrite Hm. f_equal. lia.
      * rewrite Hq. replace (edge + 8 * (t - 1)) with (edge + 8 * t - 8) by lia. exact HL.
    + destruct (zlt i n) as [Hin|]; [|reflexivity].
      destruct (Hhigh i ltac:(lia) ltac:(lia)) as [Hq Hm].
      rewrite (frame_output_bit_word _ _ _ _ _ w (Hbits i ltac:(lia))) by (rewrite Hq; exact HW).
      rewrite Hm. f_equal. lia.
Qed.

(** A decoded payload slice is exactly the encoded output word. *)
Theorem slice_word_output_encode (lg : nat) m bw edge cursor (x : Ty.tySem (Word lg)) :
  Z.of_nat (Nat.pow 2 lg) <= 64 -> Z.of_nat (Nat.pow 2 lg) <= cursor ->
  (exists p, slice_output_at (Z.of_nat (Nat.pow 2 lg)) m bw edge cursor p /\
    @fromZ (WordToZ lg) (Int64.unsigned p) = x) <->
  frame_output_cells_at m bw edge cursor (encode x).
Proof.
  intros HN HC. rewrite frame_output_word_iff.
  assert (Hpos : 1 <= Z.of_nat (Nat.pow 2 lg)).
  { pose proof (Nat.pow_nonzero 2 lg ltac:(lia)). lia. }
  split.
  - intros [p [Hp Hx]] j Hj. pose proof (proj1 (word_fromZ_bits lg x _) Hx) as Hx'. clear Hx. rename Hx' into Hx.
    rewrite <- (Hx j Hj).
    exact (slice_output_at_bits (Z.of_nat (Nat.pow 2 lg)) m bw edge cursor p ltac:(lia) HC Hp j Hj).
  - intros H. set (v := Int64.repr (@toZ (WordToZ lg) x)).
    assert (Hv : forall j, 0 <= j < Z.of_nat (Nat.pow 2 lg) ->
      Int64.testbit v j = Z.testbit (@toZ (WordToZ lg) x) j).
    { intros j Hj. unfold v. apply Int64.testbit_repr.
      change Int64.zwordsize with 64. lia. }
    exists (Int64.zero_ext (Z.of_nat (Nat.pow 2 lg)) v). split.
    + apply slice_output_at_of_bits; [lia|exact HC|].
      intros j Hj. rewrite Hv by exact Hj. apply H. exact Hj.
    + apply (proj2 (word_fromZ_bits lg x _)). intros j Hj.
      change (Z.testbit (Int64.unsigned (Int64.zero_ext (Z.of_nat (Nat.pow 2 lg)) v)) j)
        with (Int64.testbit (Int64.zero_ext (Z.of_nat (Nat.pow 2 lg)) v) j).
      rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia. apply Hv. exact Hj.
Qed.

Lemma wide_bits_pow s : wide_bits s = Z.of_nat (Nat.pow 2 (wide_log s)).
Proof. destruct s; reflexivity. Qed.

(** The 16/32/64-bit payload observation is the encoded output word. *)
Theorem wide_output_at_encode s m bw edge cursor (x : Ty.tySem (Word (wide_log s))) :
  wide_bits s <= cursor ->
  wide_output_at s m bw edge cursor x <-> frame_output_cells_at m bw edge cursor (encode x).
Proof.
  intros HC. unfold wide_output_at, decode_wide. rewrite wide_bits_pow in *.
  apply slice_word_output_encode; [destruct s; cbn; lia|exact HC].
Qed.

Lemma decode_word8_zero_ext v : decode_word8 (Int64.zero_ext 8 v) = decode_word8 v.
Proof.
  unfold decode_word8. rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia).
  exact (word_fromZ_mod 3 (Int64.unsigned v)).
Qed.

Lemma byte_output_at_slice m bw edge cursor (x : Ty.tySem Word8) :
  byte_output_at m bw edge cursor x <->
  exists p, slice_output_at 8 m bw edge cursor p /\ decode_word8 p = x.
Proof.
  unfold byte_output_at, slice_output_at.
  destruct (Z_le_dec 8 (write_word_shift cursor)) as [HNC|HCR].
  - split.
    + intros [w [HW Hx]]. eexists. split; [exists w; split; [exact HW|reflexivity]|].
      rewrite decode_word8_zero_ext. exact Hx.
    + intros [p [[w [HW <-]] Hx]]. exists w. split; [exact HW|].
      rewrite decode_word8_zero_ext in Hx. exact Hx.
  - assert (Hbyte : forall k high low, crossing_byte k high low = crossing_slice 8 k high low).
    { intros k high low. unfold crossing_byte, crossing_slice.
      replace (64 - (8 - k)) with (56 + k) by lia. reflexivity. }
    split.
    + intros [high [low [HH [HL Hx]]]]. eexists. split.
      * exists high, low. split; [exact HH|]. split; [exact HL|reflexivity].
      * rewrite <- Hbyte. exact Hx.
    + intros [p [[high [low [HH [HL <-]]]] Hx]]. exists high, low.
      split; [exact HH|]. split; [exact HL|]. rewrite Hbyte. exact Hx.
Qed.

(** The legacy byte output observation is the encoded output word. *)
Theorem byte_output_at_encode m bw edge cursor (x : Ty.tySem Word8) :
  8 <= cursor ->
  byte_output_at m bw edge cursor x <-> frame_output_cells_at m bw edge cursor (encode x).
Proof.
  intros HC. rewrite byte_output_at_slice. unfold decode_word8.
  apply (slice_word_output_encode 3); cbn; lia.
Qed.

Lemma carry_output_encode m bw edge cursor (c : Ty.tySem (Ty.Sum Ty.Unit Ty.Unit)) :
  1 <= cursor ->
  (exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w) /\
    (if Int64.testbit w ((cursor - 1) mod 64) then inr tt else inl tt) = c) <->
  frame_output_cells_at m bw edge cursor (encode c).
Proof.
  intros HC. unfold frame_output_cells_at, write_word_address.
  assert (Henc : encode c = [Some (match c with inl _ => false | inr _ => true end)])
    by (destruct c as [[]|[]]; reflexivity).
  rewrite Henc. split.
  - intros [w [HW Hc]] [|[|i]] c' Hi; cbn in Hi; try discriminate.
    injection Hi as <-. cbn [cell_matches]. split; [lia|]. exists w.
    replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. split; [exact HW|].
    subst c. destruct (Int64.testbit w ((cursor - 1) mod 64)); reflexivity.
  - intros H. specialize (H 0%nat _ eq_refl). cbn [cell_matches] in H.
    replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) in H by lia.
    destruct H as [_ [w [HW Hb]]]. exists w. split; [exact HW|].
    rewrite <- Hb. destruct c as [[]|[]]; reflexivity.
Qed.

(** Carry plus 16/32/64-bit payload: the encoded [Bit * Word] result. *)
Theorem carry_wide_output_encode s m bw edge cursor
    (v : Ty.tySem (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) (Word (wide_log s)))) :
  1 + wide_bits s <= cursor ->
  carry_wide_output_at s m bw edge cursor v <->
  frame_output_cells_at m bw edge cursor (encode v).
Proof.
  destruct v as [c x]. intros HC. unfold carry_wide_output_at.
  change (@encode (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) (Word (wide_log s))) (c, x))
    with (encode c ++ encode x).
  rewrite frame_output_cells_at_app.
  assert (Hlen : length (encode c) = 1%nat) by (destruct c as [[]|[]]; reflexivity).
  rewrite Hlen. change (Z.of_nat 1) with 1. cbn [fst snd].
  pose proof (wide_bits_bounds s).
  rewrite carry_output_encode, wide_output_at_encode by lia. reflexivity.
Qed.

(** Carry plus byte: the encoded [Bit * Word8] result. *)
Theorem carry_byte_output_encode m bw edge cursor
    (v : Ty.tySem (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word8)) :
  9 <= cursor ->
  carry_byte_output_at m bw edge cursor v <->
  frame_output_cells_at m bw edge cursor (encode v).
Proof.
  destruct v as [c x]. intros HC. unfold carry_byte_output_at.
  change (@encode (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word8) (c, x))
    with (encode c ++ encode x).
  rewrite frame_output_cells_at_app.
  assert (Hlen : length (encode c) = 1%nat) by (destruct c as [[]|[]]; reflexivity).
  rewrite Hlen. change (Z.of_nat 1) with 1. cbn [fst snd].
  rewrite carry_output_encode, byte_output_at_encode by lia. reflexivity.
Qed.
