(** Total bit writer and its bit/prefix interpretation at arbitrary output addresses. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_frame_spec C.jet_frame_arith C.jet_word_bits C.jet_carry_byte_position.
Require Import C.jet_writeBit_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma write_bit_value_correct cursor old bit : 1 <= cursor <= Int64.max_unsigned ->
  Int64.testbit (write_bit_value cursor old bit) ((cursor - 1) mod 64) = bit.
Proof.
  intros HC. pose proof (write_layout_index cursor HC) as [_ [HK _]].
  assert (HE : write_bit_value cursor old bit = carry_at (write_word_shift cursor) old bit).
  { unfold write_bit_value, carry_at.
    replace (write_word_shift cursor - 1) with ((cursor - 1) mod 64) by (unfold write_word_shift; lia).
    reflexivity. }
  rewrite HE.
  replace ((cursor - 1) mod 64) with (write_word_shift cursor - 1) by (unfold write_word_shift; lia).
  apply carry_at_bit; exact HK.
Qed.

Lemma write_bit_value_prefix cursor old bit : 1 <= cursor <= Int64.max_unsigned ->
  word_outside_eq 0 (write_word_shift cursor) (write_bit_value cursor old bit) old.
Proof.
  intros HC i HI Houtside. pose proof (write_layout_index cursor HC) as [_ [HK _]].
  unfold write_bit_value. destruct bit.
  - rewrite Int64.bits_or, Int64.bits_shl by exact HI.
    rewrite cursor_unsigned by (unfold write_word_shift in HK; lia).
    rewrite zlt_false by (unfold write_word_shift in Houtside; lia).
    rewrite Int64.bits_one. destruct (zeq (i - (cursor - 1) mod 64) 0);
      [unfold write_word_shift in Houtside; lia|apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Theorem eval_writeBit_layout m bf base bw edge cursor (bit : bool) :
  write_frame_at m bf base bw edge cursor 1 ->
  exists mf w,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) /\
    Int64.testbit w ((cursor - 1) mod 64) = bit /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 1) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (write_word_address edge cursor) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame. pose proof HFrame as [HB [[HF HO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bf base bw edge cursor 1 ltac:(lia) HFrame)
    as [HA0 [HA [PW [old HL]]]].
  pose proof (write_frame_at_head_separate m bf base bw edge cursor 1 ltac:(lia) HFrame) as HD.
  destruct (Mem.valid_access_store m Mint64 bf (base + 8) (Vlong (Int64.repr (cursor - 1))) PD)
    as [mo SO].
  assert (PWo : Mem.valid_access mo Mint64 bw (write_word_address edge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mo Mint64 bw (write_word_address edge cursor)
      (Vlong (write_bit_value cursor old bit)) PWo) as [mf SW].
  pose proof (Mem.load_store_same _ _ _ _ _ _ SW) as Hout.
  exists mf, (write_bit_value cursor old bit). split.
  - eapply eval_writeBit_layout_raw with (edge := edge); eauto; try lia. split; assumption.
  - split; [exact Hout|]. split; [apply write_bit_value_correct; lia|].
    split.
    + intros old' HL'. assert (old' = old) by congruence. subst old'.
      exists (write_bit_value cursor old bit). split; [exact Hout|apply write_bit_value_prefix; lia].
    + split.
      * split.
        -- erewrite Mem.load_store_other; [|exact SW|
             change (bf <> bw \/ base + 8 <= write_word_address edge cursor \/
               write_word_address edge cursor + 8 <= base);
             destruct HD as [HD|[HD|HD]]; [left; exact HD|right; right; exact HD|right; left; lia]].
           erewrite Mem.load_store_other; [exact HF|exact SO|right; left; change (base + 8 <= base + 8); lia].
        -- erewrite Mem.load_store_other; [|exact SW|
             change (bf <> bw \/ base + 8 + 8 <= write_word_address edge cursor \/
               write_word_address edge cursor + 8 <= base + 8);
             destruct HD as [HD|[HD|HD]]; [left; exact HD|right; right; lia|right; left; lia]]. exact (Mem.load_store_same _ _ _ _ _ _ SO).
      * split.
        -- intros chunk b ofs Hbf Hbw.
           erewrite Mem.load_store_other; [|exact SW|cbn; lia].
           eapply Mem.load_store_other; [exact SO|cbn; lia].
        -- split.
           ++ intros b ofs kind p HP. eauto using Mem.perm_store_1.
           ++ intros b HV. eauto using Mem.store_valid_block_1.
Qed.
