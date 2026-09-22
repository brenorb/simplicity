(** Two-word frame construction and nine-bit crossing frame elimination. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_spec.
Import Values Mem.
Local Open Scope Z_scope.

Lemma crossing_frame_from_words m bd bw k high low :
  1 <= k <= 7 ->
  frame_fields m bd bw 0 (64 + k) ->
  bd <> bw ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  Mem.load Mint64 m bw 8 = Some (Vlong high) ->
  Mem.load Mint64 m bw 0 = Some (Vlong low) ->
  write_frame m bd bw 0 (64 + k) 8.
Proof.
  intros HK HF HD PD PH PL HH HL.
  split; [exact HF |]. split; [lia |].
  split; [change (64 + k <= 18446744073709551615); lia |].
  split; [exact HD |]. split; [exact PD |].
  intros i HI. cbn zeta.
  assert (HA : write_cell_address 0 (64 + k) i = 0 \/
    write_cell_address 0 (64 + k) i = 8).
  { unfold write_cell_address.
    assert (HQ : 0 <= (64 + k - 1 - i) / 64 < 2).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (HQ' : (64 + k - 1 - i) / 64 = 0 \/ (64 + k - 1 - i) / 64 = 1) by lia.
    destruct HQ' as [-> | ->]; auto. }
  destruct HA as [-> | ->].
  - split; [lia |]. split; [change (0 + 8 <= 18446744073709551615); lia |].
    split; [exact PL |]. exists low; exact HL.
  - split; [lia |]. split; [change (8 + 8 <= 18446744073709551615); lia |].
    split; [exact PH |]. exists high; exact HH.
Qed.

Lemma crossing_carry_frame_words m bd bw k :
  0 <= k <= 7 ->
  write_frame m bd bw 0 (65 + k) 9 ->
  frame_fields m bd bw 0 (65 + k) /\ bd <> bw /\
  Mem.valid_access m Mint64 bd 8 Writable /\
  Mem.valid_access m Mint64 bw 8 Writable /\
  Mem.valid_access m Mint64 bw 0 Writable /\
  exists high low,
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low).
Proof.
  intros HK [HF [HC [HM [HD [PD HW]]]]].
  assert (HA : write_cell_address 0 (65 + k) 0 = 8 /\
               write_cell_address 0 (65 + k) 8 = 0).
  { assert (HE : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct HE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      split; reflexivity. }
  destruct HA as [HAH HAL].
  pose proof (HW 0 ltac:(lia)) as HH.
  pose proof (HW 8 ltac:(lia)) as HL.
  cbn zeta in HH, HL. rewrite HAH in HH. rewrite HAL in HL.
  destruct HH as [_ [_ [PH [high HH]]]].
  destruct HL as [_ [_ [PL [low HL]]]].
  split; [exact HF |]. split; [exact HD |]. split; [exact PD |].
  split; [exact PH |]. split; [exact PL |]. exists high, low; auto.
Qed.
