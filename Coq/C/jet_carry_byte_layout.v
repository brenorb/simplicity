(** Actual carry/byte calls from an arbitrary writable nine-bit output frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit C.jets C.jet_exec C.jet_spec C.jet_frame_spec C.jet_frame_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_layout_step.
Require Import C.jet_writeBit_layout_total C.jet_write8_layout_total.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition carry_byte_output_at (m : mem) (bw : block) (edge cursor : Z)
    (value : Ty.tySem (Ty.Prod Bit Word8)) : Prop :=
  (exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w) /\
    (if Int64.testbit w ((cursor - 1) mod 64) then inr tt else inl tt) = fst value) /\
  byte_output_at m bw edge (cursor - 1) (snd value).

Lemma carry_byte_output_at_preserved m mf bw edge cursor value :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  carry_byte_output_at m bw edge cursor value -> carry_byte_output_at mf bw edge cursor value.
Proof.
  intros HP [[w [HW HV]] Hbyte]. split.
  - exists w; auto.
  - eapply byte_output_at_preserved; eauto.
Qed.

Theorem eval_carry_byte_layout m bf base bw edge cursor (carry : bool) x :
  write_frame_at m bf base bw edge cursor 9 ->
  exists mb mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if carry then Int.one else Int.zero)]
      E0 mb (Vint (if carry then Int.one else Int.zero)) /\
    ClightBigstep.Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
      [Vptr bf (Ptrofs.repr base); Vint x] E0 mf Vundef /\
    carry_byte_output_at mf bw edge cursor
      (if carry then inr tt else inl tt, decode_word8 (Int64.repr (Int.unsigned x))) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 9) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (byte_write_low edge (cursor - 1)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame. pose proof HFrame as [HB [HF [HE [HC [HM [HD Hrest]]]]]].
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  assert (HFrame1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrame]; lia. }
  destruct (eval_writeBit_layout m bf base bw edge cursor carry HFrame1)
    as [mb [bithigh [HBit [HBitLoad [HBitValue [HPrefix1 [HFields1 [HMem1 [HPerm1 HValid1]]]]]]]]].
  assert (HFrame8 : write_frame_at mb bf base bw edge (cursor - 1) 8).
  { eapply write_frame_at_after_bit; eauto; lia. }
  destruct (eval_write8_layout mb bf base bw edge (cursor - 1) x HFrame8)
    as [mf [HByte [HByteValue [HPrefix8 [HFields8 [HMem8 [HPerm8 HValid8]]]]]]].
  assert (HHead : exists w,
    Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) /\
    word_outside_eq 0 (write_word_shift cursor - 1) w bithigh).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [Hshift Haddr].
      exists bithigh. split.
      + rewrite HMem8; [exact HBitLoad|left; congruence|right; right]. rewrite Haddr; lia.
      + intros i Hi Hout; reflexivity.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [Hshift Haddr].
      unfold write_prefix_at in HPrefix8. rewrite Hshift, Haddr in HPrefix8.
      exact (HPrefix8 bithigh HBitLoad). }
  destruct HHead as [outputhigh [HHigh HSame]].
  assert (HPrev : write_word_address edge (cursor - 1) <= write_word_address edge cursor).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [_ Haddr]. lia.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [_ Haddr]. lia. }
  assert (HLow : byte_write_low edge (cursor - 1) <= write_word_address edge cursor).
  { unfold byte_write_low. destruct (Z_le_dec 8 (write_word_shift (cursor - 1))); lia. }
  exists mb, mf. split; [exact HBit|]. split; [exact HByte|].
  split.
  - split; [|exact HByteValue]. exists outputhigh. split; [exact HHigh|].
    rewrite HSame.
    + rewrite HBitValue; reflexivity.
    + unfold write_word_shift in HK; lia.
    + right. unfold write_word_shift; lia.
  - split.
    + intros old HL. destruct (HPrefix1 old HL) as [w [HW HOld]].
      assert (w = bithigh) by congruence. subst w.
      exists outputhigh. split; [exact HHigh|]. intros i Hi Hout.
      rewrite HSame; [apply HOld; assumption|exact Hi|lia].
    + split.
      * replace (cursor - 9) with (cursor - 1 - 8) by lia. exact HFields8.
      * split.
        -- intros chunk b ofs Hbf Hbw. rewrite HMem8; [|exact Hbf|lia].
           apply HMem1; [exact Hbf|lia].
        -- split.
           ++ intros b ofs kind p HP. apply HPerm8; apply HPerm1; exact HP.
           ++ intros b HV. apply HValid8; apply HValid1; exact HV.
Qed.
