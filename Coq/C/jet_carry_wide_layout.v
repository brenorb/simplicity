(** Actual carry plus 16/32/64-bit payload calls on arbitrary output frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_spec.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_output_layout_step C.jet_writeBit_layout_total.
Require Import C.jet_write_wide_layout_total C.jet_wide C.jet_wide_spec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition carry_wide_output_at s (m : mem) (bw : block) (edge cursor : Z)
    (value : Ty.tySem (Ty.Prod Bit (Word (wide_log s)))) : Prop :=
  (exists w, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong w) /\
    (if Int64.testbit w ((cursor - 1) mod 64) then inr tt else inl tt) = fst value) /\
  wide_output_at s m bw edge (cursor - 1) (snd value).

Lemma carry_wide_output_at_preserved s m mf bw edge cursor value :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  carry_wide_output_at s m bw edge cursor value ->
  carry_wide_output_at s mf bw edge cursor value.
Proof.
  intros HP [[w [HW HC]] Hwide]. split.
  - exists w; auto.
  - eapply wide_output_at_preserved; eauto.
Qed.

Theorem eval_carry_wide_layout (s : wide_size) m bf base bw edge cursor
    (carry : bool) (payload : int64) :
  write_frame_at m bf base bw edge cursor (1 + wide_bits s) ->
  exists mb mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if carry then Int.one else Int.zero)]
      E0 mb (Vint (if carry then Int.one else Int.zero)) /\
    ClightBigstep.Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong payload] E0 mf Vundef /\
    carry_wide_output_at s mf bw edge cursor
      (if carry then inr tt else inl tt,
        decode_wide s (Int64.zero_ext (wide_bits s) payload)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - (1 + wide_bits s)) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (slice_write_low (wide_bits s) edge (cursor - 1))
        (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame.
  pose proof (wide_bits_bounds s) as HN.
  pose proof HFrame as [HB [HF [HE [HC [HM [PD HW]]]]]].
  pose proof (write_frame_at_head_separate m bf base bw edge cursor (1 + wide_bits s) ltac:(lia) HFrame) as HD.
  assert (HFrameNext : write_frame_at m bf base bw edge cursor (wide_bits s + 1)).
  { replace (wide_bits s + 1) with (1 + wide_bits s) by lia. exact HFrame. }
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  assert (HFrame1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrame]; pose proof (wide_bits_bounds s); lia. }
  destruct (eval_writeBit_layout m bf base bw edge cursor carry HFrame1)
    as [mb [bithigh [HBit [HBitLoad [HBitValue [HPrefix1
      [HFields1 [HMem1 [HPerm1 HValid1]]]]]]]]].
  assert (HFrameWide : write_frame_at mb bf base bw edge (cursor - 1) (wide_bits s)).
  { eapply write_frame_at_after_bit with (w := bithigh).
    - pose proof (wide_bits_bounds s); lia.
    - exact HFrameNext.
    - exact HFields1.
    - exact HBitLoad.
    - exact HMem1.
    - exact HPerm1. }
  destruct (eval_write_wide_layout s mb bf base bw edge (cursor - 1) payload HFrameWide)
    as [mf [HWrite [HOutput [HPrefixWide [HFieldsWide [HMemWide
      [HPermWide HValidWide]]]]]]].
  assert (HHead : exists w,
      Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) /\
      word_outside_eq 0 (write_word_shift cursor - 1) w bithigh).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [Hshift Haddr].
      exists bithigh. split.
      + rewrite HMemWide; [exact HBitLoad|
          change (bw <> bf \/ write_word_address edge cursor + 8 <= base + 8 \/
            base + 16 <= write_word_address edge cursor);
          destruct HD as [HD|[HD|HD]]; [left; congruence|right; left; lia|right; right; exact HD]
        |right; right].
        rewrite Haddr. lia.
      + intros i Hi Hout. reflexivity.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [Hshift Haddr].
      unfold write_prefix_at in HPrefixWide. rewrite Hshift, Haddr in HPrefixWide.
      exact (HPrefixWide bithigh HBitLoad). }
  destruct HHead as [outputhigh [HHigh HSame]].
  assert (HPrev : write_word_address edge (cursor - 1) <= write_word_address edge cursor).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [_ Haddr]. lia.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [_ Haddr]. lia. }
  assert (HLow : slice_write_low (wide_bits s) edge (cursor - 1) <=
      write_word_address edge cursor).
  { unfold slice_write_low. destruct (Z_le_dec (wide_bits s)
        (write_word_shift (cursor - 1))); lia. }
  exists mb, mf. split; [exact HBit|]. split; [exact HWrite|].
  split.
  - split; [|].
    + exists outputhigh. split; [exact HHigh|].
      rewrite HSame.
      * rewrite HBitValue. reflexivity.
      * unfold write_word_shift in HK. lia.
      * right. unfold write_word_shift. lia.
    + unfold wide_output_at. exists (Int64.zero_ext (wide_bits s) payload).
      split; [exact HOutput|reflexivity].
  - split.
    + intros old HL. destruct (HPrefix1 old HL) as [w [HW' HOld]].
      assert (w = bithigh) by congruence. subst w.
      exists outputhigh. split; [exact HHigh|].
      intros i Hi Hout. rewrite HSame; [apply HOld; assumption|exact Hi|lia].
    + split.
      * replace (cursor - (1 + wide_bits s)) with
        (cursor - 1 - wide_bits s) by lia. exact HFieldsWide.
      * split.
        -- intros chunk b ofs Hbf Hbw.
        assert (HbfWide : b <> bf \/ ofs + size_chunk chunk <= base + 8 \/
            base + 16 <= ofs) by exact Hbf.
        assert (HbwWide : b <> bw \/
            ofs + size_chunk chunk <= slice_write_low (wide_bits s) edge (cursor - 1) \/
            write_word_address edge (cursor - 1) + 8 <= ofs).
        { destruct Hbw as [Hneq|[Hbefore|Hafter]].
          - left; exact Hneq.
          - right; left; lia.
          - right; right; lia. }
        assert (HbwBit : b <> bw \/
            ofs + size_chunk chunk <= write_word_address edge cursor \/
            write_word_address edge cursor + 8 <= ofs).
        { destruct Hbw as [Hneq|[Hbefore|Hafter]].
          - left; exact Hneq.
          - right; left; lia.
          - right; right; exact Hafter. }
        rewrite HMemWide; [|exact HbfWide|exact HbwWide].
        apply HMem1; [exact Hbf|exact HbwBit].
        -- split.
           ++ intros b ofs kind p HP. apply HPermWide, HPerm1. exact HP.
           ++ intros b HV. apply HValidWide, HValid1. exact HV.
Qed.
