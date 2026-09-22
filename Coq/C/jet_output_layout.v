(** Writable frames and output observations at arbitrary physical addresses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_spec C.jet_crossing_word.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Definition write_frame_at (m : mem) (bf : block) (base : Z) (bw : block)
    (edge cursor count : Z) : Prop :=
  frame_base_valid base /\ frame_fields_at m bf base bw edge cursor /\
  0 <= edge /\ 0 <= count <= cursor /\ cursor <= Int64.max_unsigned /\ bf <> bw /\
  Mem.valid_access m Mint64 bf (base + 8) Writable /\
  forall i, 0 <= i < count ->
    let addr := write_cell_address edge cursor i in
    0 <= addr /\ addr + 8 <= Ptrofs.max_unsigned /\
    Mem.valid_access m Mint64 bw addr Writable /\
    exists w, Mem.load Mint64 m bw addr = Some (Vlong w).

Definition byte_output_at (m : mem) (bw : block) (edge cursor : Z) (x : Ty.tySem Word.Word8) : Prop :=
  if Z_le_dec 8 (write_word_shift cursor) then
    exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w) /\
      decode_word8 (Int64.shru w (Int64.repr (write_word_shift cursor - 8))) = x
  else exists high low,
    Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong high) /\
    Mem.load Mint64 m bw (write_word_address edge cursor - 8) = Some (Vlong low) /\
    decode_word8 (crossing_byte (write_word_shift cursor) high low) = x.

Definition write_prefix_at (m mf : mem) (bw : block) (edge cursor : Z) : Prop :=
  forall old, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
    exists w, Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) /\
      word_outside_eq 0 (write_word_shift cursor) w old.

(** Loads outside two modified byte intervals, including within their blocks. *)
Definition loads_outside_ranges (m mf : mem) (bf : block) (flo fhi : Z)
    (bw : block) (wlo whi : Z) : Prop :=
  forall chunk b ofs,
    (b <> bf \/ ofs + size_chunk chunk <= flo \/ fhi <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= wlo \/ whi <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs.

Definition byte_write_low edge cursor :=
  if Z_le_dec 8 (write_word_shift cursor)
  then write_word_address edge cursor else write_word_address edge cursor - 8.

Lemma write_word_crossing_address edge cursor k :
  8 <= cursor -> 1 <= k <= 7 -> write_word_shift cursor = k ->
  write_cell_address edge cursor k = write_word_address edge cursor - 8.
Proof.
  intros HC HK Hshift.
  pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)) as Hdiv.
  unfold write_word_shift in Hshift.
  assert (Hq : (cursor - 1 - k) / 64 = (cursor - 1) / 64 - 1).
  { symmetry. apply Z.div_unique with (r := 63); lia. }
  unfold write_cell_address, write_word_address. rewrite Hq. lia.
Qed.

Lemma write_frame_at_preserved m mf bf base bw edge cursor count :
  (forall chunk b ofs v, b = bf \/ b = bw -> Mem.load chunk m b ofs = Some v ->
    Mem.load chunk mf b ofs = Some v) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  write_frame_at m bf base bw edge cursor count -> write_frame_at mf bf base bw edge cursor count.
Proof.
  intros HL HP [HB [[HE HO] [Hedge [HC [HM [HD [PF HW]]]]]]].
  assert (HV : forall chunk b ofs p, Mem.valid_access m chunk b ofs p -> Mem.valid_access mf chunk b ofs p).
  { intros chunk b ofs p [HR HA]. split; [|exact HA]. intros addr HA'. apply HP. apply HR; exact HA'. }
  split; [exact HB|]. split; [split; eapply HL; eauto|].
  split; [exact Hedge|]. split; [exact HC|]. split; [exact HM|]. split; [exact HD|].
  split; [auto|]. intros i Hi. destruct (HW i Hi) as [HA0 [HAM [PW [w Hword]]]].
  split; [exact HA0|]. split; [exact HAM|]. split; [auto|]. exists w. eapply HL; eauto.
Qed.

Lemma byte_output_at_preserved m mf bw edge cursor x :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) -> Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  byte_output_at m bw edge cursor x -> byte_output_at mf bw edge cursor x.
Proof.
  intros HP. unfold byte_output_at. destruct (Z_le_dec 8 (write_word_shift cursor)).
  - intros [w [HW HX]]. exists w; auto.
  - intros [h [l [HH [HL HX]]]]. exists h, l; auto.
Qed.

Lemma write_prefix_at_preserved m mr me mf bw edge cursor :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) -> Mem.load Mint64 mr bw ofs = Some (Vlong w)) ->
  (forall ofs w, Mem.load Mint64 me bw ofs = Some (Vlong w) -> Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  write_prefix_at mr me bw edge cursor -> write_prefix_at m mf bw edge cursor.
Proof.
  intros HI HO HP old HL. destruct (HP old (HI _ _ HL)) as [w [HW HE]]. exists w; auto.
Qed.

Lemma write_frame_at_head m bf base bw edge cursor count :
  0 < count -> write_frame_at m bf base bw edge cursor count ->
  0 <= write_word_address edge cursor /\ write_word_address edge cursor + 8 <= Ptrofs.max_unsigned /\
  Mem.valid_access m Mint64 bw (write_word_address edge cursor) Writable /\
  exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w).
Proof.
  intros HC [_ [_ [_ [_ [_ [_ [_ HW]]]]]]]. specialize (HW 0 ltac:(lia)).
  unfold write_cell_address in HW. rewrite Z.sub_0_r in HW. exact HW.
Qed.

Lemma write_frame_at_crossing m bf base bw edge cursor :
  write_word_shift cursor < 8 -> write_frame_at m bf base bw edge cursor 8 ->
  8 <= write_word_address edge cursor /\
  Mem.valid_access m Mint64 bw (write_word_address edge cursor - 8) Writable /\
  exists w, Mem.load Mint64 m bw (write_word_address edge cursor - 8) = Some (Vlong w).
Proof.
  intros Hcross [_ [_ [_ [HC [HM [_ [_ HW]]]]]]].
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  specialize (HW (write_word_shift cursor) ltac:(lia)). cbn zeta in HW.
  rewrite write_word_crossing_address in HW by lia.
  destruct HW as [HL [_ HW]]. split; [lia|exact HW].
Qed.
