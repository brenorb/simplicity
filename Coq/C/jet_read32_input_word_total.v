(** Initial-memory read32 contract for arbitrary logical Word32 inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_read32_input_word C.jet_read32_layout_total.
Require Import C.jet_read16_input_word C.jet_frame_arith.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma read32_layout_value_unsigned m bw edge cursor high low
    (x : Ty.tySem (Word 5)) :
  0 <= cursor ->
  frame_input_word_at m bw edge cursor x ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (32 < cursor mod 64 ->
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Int64.unsigned (read32_layout_value cursor high low) =
    @toZ (WordToZ 5) x.
Proof.
  intros HC Hinput Hhigh Hlow.
  unfold read32_layout_value.
  destruct (Z_le_dec (cursor mod 64) 32) as [Hnoncross|Hcross].
  - exact (read32_non_crossing_at_unsigned m bw edge cursor high x
      HC Hnoncross Hinput Hhigh).
  - assert (Hcrossing : 32 < cursor mod 64 < 64).
    { pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)). lia. }
    exact (read32_crossing_at_unsigned m bw edge cursor high low x
      HC Hcrossing Hinput Hhigh (Hlow ltac:(lia))).
Qed.

Lemma read32_input_loads m bw edge cursor (x : Ty.tySem (Word 5)) :
  0 <= cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bw edge cursor x ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned /\
  exists high low,
    Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) /\
    (32 < cursor mod 64 ->
      8 * (2 + cursor / 64) <= edge /\
      Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)).
Proof.
  intros HC Hinput.
  pose proof (frame_input_word_at_bit32 m bw edge cursor x 0 Hinput ltac:(lia)) as Hfirst.
  replace (cursor + Z.of_nat 0) with cursor in Hfirst by lia.
  destruct Hfirst as [_ [HE [high [HH _]]]].
  split; [exact HE|].
  destruct (Z_lt_dec 32 (cursor mod 64)) as [HX|HN].
  - set (k := 64 - cursor mod 64).
    assert (HK : 1 <= k <= 31) by
      (unfold k; pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia).
    assert (Hnat : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    assert (Hi : (Z.to_nat k < 32)%nat).
    { apply Nat2Z.inj_lt. rewrite Hnat. lia. }
    pose proof (frame_input_word_at_bit32 m bw edge cursor x (Z.to_nat k)
      Hinput Hi) as Hnext.
    unfold frame_input_bit_at in Hnext.
    rewrite Hnat in Hnext.
    destruct Hnext as [_ [HElow [low [HL _]]]].
    destruct (cursor_add_index_crossing cursor k
      ltac:(lia) ltac:(lia) ltac:(unfold k; lia) ltac:(unfold k; lia))
      as [HQ HR].
    rewrite HQ in HElow, HL.
    replace (1 + (cursor / 64 + 1)) with (2 + cursor / 64)
      in HElow, HL by lia.
    exists high, low. split; [exact HH|].
    intros _. split; [exact (proj1 HElow)|exact HL].
  - exists high, Int64.zero.
    split; [exact HH|]. intros Hbad. lia.
Qed.

Theorem eval_read32_word_at m bf base bw edge cursor
    (x : Ty.tySem (Word 5)) :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 32 ->
  frame_fields_at m bf base bw edge cursor ->
  frame_input_word_at m bw edge cursor x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf r,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read32)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ 5) x /\
    frame_fields_at mf bf base bw edge (cursor + 32) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/
      base + 16 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HF Hinput PW Hsep.
  destruct (read32_input_loads m bw edge cursor x HC Hinput)
    as [HE [high [low [Hhigh Hlow]]]].
  destruct (eval_read32_layout_total m bf base bw edge cursor high low
      HB HC HE HF Hhigh Hlow PW Hsep)
    as [mf [Heval [Hfields [Hloads [Hperm Hblocks]]]]].
  exists mf, (read32_layout_value cursor high low).
  split; [exact Heval|].
  split.
  - exact (read32_layout_value_unsigned m bw edge cursor high low x
      ltac:(lia) Hinput Hhigh (fun Hcross => proj2 (Hlow Hcross))).
  - split; [exact Hfields|].
    split; [exact Hloads|].
    split; [exact Hperm|exact Hblocks].
Qed.
