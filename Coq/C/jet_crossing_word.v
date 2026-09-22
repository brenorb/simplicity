(** Interpret a byte split across adjacent 64-bit backing words. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers AST Memory.
Require Import C.jet_frame_spec C.jet_word_bits C.jet_crossing_arith
  C.jet_spec C.jet_word_decode.
Import Values Mem.
Local Open Scope Z_scope.

Definition crossing_byte (k : Z) (high low : int64) : int64 :=
  Int64.or (Int64.shl (Int64.zero_ext k high) (Int64.repr (8 - k)))
    (Int64.shru low (Int64.repr (56 + k))).

Lemma clear_low_projection k w : 1 <= k <= 64 ->
  Int64.zero_ext k (clear_low k w) = Int64.zero.
Proof.
  intros HK. apply Int64.same_bits_eq. intros i HI.
  change (0 <= i < 64) in HI.
  rewrite Int64.bits_zero_ext by lia.
  rewrite clear_low_bits by lia. rewrite Int64.bits_zero.
  destruct (zlt i k); reflexivity.
Qed.

Lemma crossing_byte_one k old :
  1 <= k <= 7 ->
  decode_word8 (crossing_byte k (clear_low k old)
    (Int64.shl Int64.one (Int64.repr (56 + k)))) = @one8_spec Alg.CoreFunSem tt.
Proof.
  intros HK. unfold crossing_byte.
  rewrite clear_low_projection by lia.
  assert (HC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
    exact decode_word8_one.
Qed.

Lemma clear_low_prefix k old : 1 <= k <= 64 ->
  word_outside_eq 0 k (clear_low k old) old.
Proof.
  intros HK i HI [HL|HG]; [lia|].
  rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Lemma crossing_frame_words m bd bw k :
  1 <= k <= 7 ->
  write_frame m bd bw 0 (64 + k) 8 ->
  frame_fields m bd bw 0 (64 + k) /\ bd <> bw /\
  Mem.valid_access m Mint64 bd 8 Writable /\
  Mem.valid_access m Mint64 bw 8 Writable /\
  Mem.valid_access m Mint64 bw 0 Writable /\
  exists high low,
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low).
Proof.
  intros HK [HF [HC [HM [HD [PD HW]]]]].
  assert (HA : write_cell_address 0 (64 + k) 0 = 8 /\
               write_cell_address 0 (64 + k) 7 = 0).
  { assert (HE : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct HE as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]];
      split; reflexivity. }
  destruct HA as [HAH HAL].
  pose proof (HW 0 ltac:(lia)) as HH.
  pose proof (HW 7 ltac:(lia)) as HL.
  cbn zeta in HH, HL. rewrite HAH in HH. rewrite HAL in HL.
  destruct HH as [_ [_ [PH [high HH]]]].
  destruct HL as [_ [_ [PL [low HL]]]].
  split; [exact HF |]. split; [exact HD |]. split; [exact PD |].
  split; [exact PH |]. split; [exact PL |]. exists high, low; auto.
Qed.
