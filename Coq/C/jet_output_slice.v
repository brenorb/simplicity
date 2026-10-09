(** Width-independent output observations and writable crossing-word access. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_word_slice.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

(** [x] is the extracted, zero-extended n-bit payload, not the entire backing
    word. Prefix bits are deliberately excluded from this observation. *)
Definition slice_output_at n (m : mem) bw edge cursor x : Prop :=
  if Z_le_dec n (write_word_shift cursor) then
    exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w) /\
      Int64.zero_ext n (Int64.shru w (Int64.repr (write_word_shift cursor - n))) = x
  else exists high low,
    Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong high) /\
    Mem.load Mint64 m bw (write_word_address edge cursor - 8) = Some (Vlong low) /\
    crossing_slice n (write_word_shift cursor) high low = x.

Definition slice_write_low n edge cursor :=
  if Z_le_dec n (write_word_shift cursor)
  then write_word_address edge cursor else write_word_address edge cursor - 8.

Lemma slice_output_at_preserved n m mf bw edge cursor x :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) -> Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  slice_output_at n m bw edge cursor x -> slice_output_at n mf bw edge cursor x.
Proof.
  intros HP. unfold slice_output_at. destruct (Z_le_dec n (write_word_shift cursor)).
  - intros [w [HW HX]]. exists w; auto.
  - intros [h [l [HH [HL HX]]]]. exists h, l; auto.
Qed.

Lemma slice_crossing_address edge cursor k :
  write_word_shift cursor = k ->
  write_cell_address edge cursor k = write_word_address edge cursor - 8.
Proof.
  intros Hshift. pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)) as Hdiv.
  unfold write_word_shift in Hshift.
  assert (Hq : (cursor - 1 - k) / 64 = (cursor - 1) / 64 - 1).
  { symmetry. apply Z.div_unique with (r := 63); lia. }
  unfold write_cell_address, write_word_address. rewrite Hq. lia.
Qed.

Lemma write_frame_at_slice_crossing n m bf base bw edge cursor :
  write_word_shift cursor < n -> write_frame_at m bf base bw edge cursor n ->
  8 <= write_word_address edge cursor /\
  Mem.valid_access m Mint64 bw (write_word_address edge cursor - 8) Writable /\
  exists w, Mem.load Mint64 m bw (write_word_address edge cursor - 8) = Some (Vlong w).
Proof.
  intros Hcross (HB & HF & HE & HC & HM & PF & HW).
  assert (HK : 1 <= write_word_shift cursor <= 64).
  { unfold write_word_shift. pose proof (Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)); lia. }
  specialize (HW (write_word_shift cursor) ltac:(lia)). cbn zeta in HW.
  rewrite slice_crossing_address in HW by reflexivity.
  destruct HW as (HA0 & HA & HD & PW & HL). split; [lia|]. split; assumption.
Qed.

Lemma write_frame_at_slice_crossing_separate n m bf base bw edge cursor :
  write_word_shift cursor < n -> write_frame_at m bf base bw edge cursor n ->
  bf <> bw \/ write_word_address edge cursor - 8 + 8 <= base \/
    base + 16 <= write_word_address edge cursor - 8.
Proof.
  intros Hcross (HB & HF & HE & HC & HM & PF & HW).
  assert (HK : 1 <= write_word_shift cursor <= 64).
  { unfold write_word_shift. pose proof (Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)); lia. }
  specialize (HW (write_word_shift cursor) ltac:(lia)). cbn zeta in HW.
  rewrite slice_crossing_address in HW by reflexivity.
  exact (proj1 (proj2 (proj2 HW))).
Qed.
