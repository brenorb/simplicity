(** Byte-sequence representation for arbitrary input frame addresses.
    Only the represented byte slices are constrained, never unrelated bits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_spec C.jet_read8.
Require Import C.jet_frame_layout C.jet_read8_layout_total.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition byte_slice_at (m : mem) (bw : block) (edge cursor : Z)
    (x : Ty.tySem Word8) : Prop :=
  0 <= cursor <= Int64.max_unsigned - 8 /\
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned /\
  exists high low,
    Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) /\
    (56 < cursor mod 64 ->
      8 * (2 + cursor / 64) <= edge /\
      Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) /\
    decode_word8 (read8_layout_byte cursor high low) = x.

Definition byte_input_at (m : mem) (bf : block) (base : Z)
    (bw : block) (edge cursor : Z) (xs : list (Ty.tySem Word8)) : Prop :=
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  forall i x, nth_error xs i = Some x ->
    byte_slice_at m bw edge (cursor + 8 * Z.of_nat i) x.

(** A logical input bit is the bit encountered at absolute frame cursor [q].
    This predicate describes the MSB-first frame stream directly, independently
    of any C reader's extraction and alignment branches. *)
Definition frame_input_bit_at (m : mem) (bw : block) (edge q : Z) (b : bool) : Prop :=
  0 <= q <= Int64.max_unsigned /\
  8 * (1 + q / 64) <= edge <= Ptrofs.max_unsigned /\
  exists w,
    Mem.load Mint64 m bw (edge - 8 * (1 + q / 64)) = Some (Vlong w) /\
    b = Z.testbit (Int64.unsigned w) (63 - q mod 64).

(** A list of logical input bits beginning at [cursor]. The suffix can be
    retained and reused after consuming a prefix. *)
Definition frame_input_bits_at (m : mem) (bw : block) (edge cursor : Z)
    (bits : list bool) : Prop :=
  forall i b, nth_error bits i = Some b ->
    frame_input_bit_at m bw edge (cursor + Z.of_nat i) b.

Definition frame_input_word_bits {n : nat} (value : Ty.tySem (Word n)) : list bool :=
  map (fun i => Z.testbit (@toZ (WordToZ n) value)
       (Z.of_nat (Nat.pow 2 n - S i))) (seq 0 (Nat.pow 2 n)).

Lemma frame_input_word_bits_length {n : nat} (value : Ty.tySem (Word n)) :
  length (frame_input_word_bits value) = Nat.pow 2 n.
Proof. unfold frame_input_word_bits. rewrite map_length, seq_length. reflexivity. Qed.

Definition frame_input_word_at {n : nat} (m : mem) (bw : block)
    (edge cursor : Z) (value : Ty.tySem (Word n)) : Prop :=
  frame_input_bits_at m bw edge cursor (frame_input_word_bits value).

Lemma frame_input_bits_at_app m bw edge cursor xs ys :
  frame_input_bits_at m bw edge cursor (xs ++ ys) <->
  frame_input_bits_at m bw edge cursor xs /\
  frame_input_bits_at m bw edge (cursor + Z.of_nat (length xs)) ys.
Proof.
  unfold frame_input_bits_at.
  split.
  - intros H. split.
    + intros i b Hi. apply (H i b). rewrite nth_error_app1; [exact Hi|].
      apply nth_error_Some. rewrite Hi. discriminate.
    + intros i b Hi.
      assert (Hnth : nth_error (xs ++ ys) (length xs + i)%nat = Some b).
      { rewrite nth_error_app2 by lia.
        replace (length xs + i - length xs)%nat with i by lia. exact Hi. }
      pose proof (H (length xs + i)%nat b Hnth) as Hbit.
      replace (cursor + Z.of_nat (length xs + i)) with
        (cursor + Z.of_nat (length xs) + Z.of_nat i) in Hbit by
        (rewrite Nat2Z.inj_add; lia).
      exact Hbit.
  - intros [HX HY] i b Hi.
    destruct (nth_error xs i) as [x|] eqn:EX.
    + assert (Hsmall : (i < length xs)%nat)
        by (apply nth_error_Some; rewrite EX; discriminate).
      rewrite nth_error_app1 in Hi by exact Hsmall.
      rewrite EX in Hi. inversion Hi; subst b.
      apply HX; exact EX.
    + assert (Hlen : (length xs <= i)%nat) by (apply nth_error_None; exact EX).
      rewrite nth_error_app2 in Hi by exact Hlen.
      specialize (HY (i - length xs)%nat b Hi).
      rewrite Nat2Z.inj_sub in HY by exact Hlen.
      replace (cursor + Z.of_nat (length xs) +
        (Z.of_nat i - Z.of_nat (length xs)))
        with (cursor + Z.of_nat i) in HY by lia.
      exact HY.
Qed.

Lemma frame_input_bit_at_preserved m mf bw edge cursor bit :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  frame_input_bit_at m bw edge cursor bit ->
  frame_input_bit_at mf bw edge cursor bit.
Proof.
  intros Hloads [HQ [HE [w [HL Hb]]]].
  split; [exact HQ|]. split; [exact HE|]. exists w. split; [eauto|exact Hb].
Qed.

Lemma frame_input_bits_at_preserved m mf bw edge cursor bits :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  frame_input_bits_at m bw edge cursor bits ->
  frame_input_bits_at mf bw edge cursor bits.
Proof.
  intros Hloads Hbits i b Hi. eapply frame_input_bit_at_preserved; eauto.
Qed.

Lemma byte_input_single_at m bf base bw edge cursor x :
  byte_input_at m bf base bw edge cursor [x] ->
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  byte_slice_at m bw edge cursor x.
Proof.
  intros [HB [HF HX]]. split; [exact HB|]. split; [exact HF|].
  specialize (HX O x eq_refl). replace (cursor + 8 * Z.of_nat O) with cursor in HX by lia.
  exact HX.
Qed.

Lemma byte_input_pair_at m bf base bw edge cursor x y :
  byte_input_at m bf base bw edge cursor [x; y] ->
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  byte_slice_at m bw edge cursor x /\ byte_slice_at m bw edge (cursor + 8) y.
Proof.
  intros [HB [HF HX]]. split; [exact HB|]. split; [exact HF|]. split.
  - specialize (HX O x eq_refl). replace (cursor + 8 * Z.of_nat O) with cursor in HX by lia. exact HX.
  - specialize (HX (S O) y eq_refl).
    replace (cursor + 8 * Z.of_nat (S O)) with (cursor + 8) in HX by lia. exact HX.
Qed.

Lemma byte_slice_preserved m mf bw edge cursor x :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  byte_slice_at m bw edge cursor x -> byte_slice_at mf bw edge cursor x.
Proof.
  intros HP [HC [HE [high [low [HH [HL HX]]]]]].
  split; [exact HC|]. split; [exact HE|]. exists high, low.
  split; [auto|]. split; [|exact HX]. intros Hcross.
  destruct (HL Hcross); auto.
Qed.

Theorem eval_read8_byte_at m bf base bw edge cursor x :
  frame_base_valid base -> frame_fields_at m bf base bw edge cursor ->
  byte_slice_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf payload,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (read8_result payload)) /\
    decode_word8 payload = x /\ frame_fields_at mf bf base bw edge (cursor + 8) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HF [HC [HE [high [low [HH [HL HX]]]]]] PW HD.
  destruct (eval_read8_layout m bf base bw edge cursor high low HB HC HE HF HH HL PW HD)
    as [mf [Hcall Hrest]].
  exists mf, (read8_layout_byte cursor high low). split; [exact Hcall|].
  split; assumption.
Qed.
