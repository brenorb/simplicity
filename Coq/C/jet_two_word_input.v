(** Shared representation for byte sequences within two backing words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.Word C.jet_spec C.jet_frame_spec C.jet_read8_two_words.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Definition two_word_input (m : mem) (bf bw : block) (cursor : Z)
    (xs : list (Ty.tySem Word8)) : Prop :=
  frame_fields m bf bw 16 cursor /\
  0 <= cursor /\ cursor + 8 * Z.of_nat (length xs) <= 128 /\
  exists high low,
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low) /\
    (forall i x, nth_error xs i = Some x ->
      decode_word8 (two_word_byte (cursor + 8 * Z.of_nat i) high low) = x).

Lemma two_word_input_single m bf bw cursor x :
  two_word_input m bf bw cursor [x] ->
  exists high low,
    frame_fields m bf bw 16 cursor /\ 0 <= cursor <= 120 /\
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low) /\
    decode_word8 (two_word_byte cursor high low) = x.
Proof.
  intros [HF [HC [HB [high [low [HH [HL HX]]]]]]].
  exists high, low. split; [exact HF |].
  split; [change (cursor + 8 * 1 <= 128) in HB; lia |].
  split; [exact HH |]. split; [exact HL |].
  specialize (HX 0%nat x eq_refl).
  replace (cursor + 8 * Z.of_nat 0) with cursor in HX by lia. exact HX.
Qed.

Lemma two_word_input_pair m bf bw cursor x y :
  two_word_input m bf bw cursor [x; y] ->
  exists high low,
    frame_fields m bf bw 16 cursor /\ 0 <= cursor <= 112 /\
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low) /\
    decode_word8 (two_word_byte cursor high low) = x /\
    decode_word8 (two_word_byte (cursor + 8) high low) = y.
Proof.
  intros [HF [HC [HB [high [low [HH [HL HX]]]]]]].
  exists high, low. split; [exact HF |].
  split; [change (cursor + 8 * 2 <= 128) in HB; lia |].
  split; [exact HH |]. split; [exact HL |].
  pose proof (HX 0%nat x eq_refl) as Hx.
  pose proof (HX 1%nat y eq_refl) as Hy.
  replace (cursor + 8 * Z.of_nat 0) with cursor in Hx by lia.
  replace (cursor + 8 * Z.of_nat 1) with (cursor + 8) in Hy by lia. auto.
Qed.

Lemma permissions_preserve_access m mf :
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
    Mem.valid_access mf chunk b ofs p.
Proof.
  intros HP chunk b ofs p [HR HA]. split; [|exact HA].
  intros ofs' Hrange. apply HP. apply HR; exact Hrange.
Qed.

Lemma permissions_preserve_valid_block m mf :
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.valid_block mf b.
Proof. intros HP b ofs kind p H. eapply Mem.perm_valid_block; eauto. Qed.
