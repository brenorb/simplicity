(** Complete byte writes from initial frame permissions, at arbitrary addresses. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_frame_spec C.jet_spec C.jet_write8_layout C.jet_write8_position.
Require Import C.jet_word_position C.jet_word_decode C.jet_crossing_word C.jet_crossing_byte.
Require Import C.jet_write8_crossing_general.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_write8_layout m bf base bw edge cursor x :
  write_frame_at m bf base bw edge cursor 8 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bf (Ptrofs.repr base); Vint x] E0 mf Vundef /\
    byte_output_at mf bw edge cursor (decode_word8 (Int64.repr (Int.unsigned x))) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 8) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (byte_write_low edge cursor) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame.
  pose proof HFrame as [HB [[HF HO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bf base bw edge cursor 8 ltac:(lia) HFrame)
    as [HA0 [HA [PH [oldhigh HH]]]].
  pose proof (write_frame_at_head_separate m bf base bw edge cursor 8 ltac:(lia) HFrame) as HD.
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  unfold byte_output_at, byte_write_low.
  destruct (Z_le_dec 8 (write_word_shift cursor)) as [HN | HX].
  - set (output := put_byte (write_word_shift cursor) oldhigh (Int64.repr (Int.unsigned x))).
    destruct (Mem.valid_access_store m Mint64 bw (write_word_address edge cursor) (Vlong output) PH)
      as [mw SW].
    assert (PDw : Mem.valid_access mw Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mw Mint64 bf (base + 8) (Vlong (Int64.repr (cursor - 8))) PDw)
      as [mf SF].
    assert (Houtput : Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong output)).
    { erewrite frame_store_preserves_word_load; [|eassumption|exact SF]. exact (Mem.load_store_same _ _ _ _ _ _ SW). }
    exists mf. split.
    + eapply eval_write8_layout_non_crossing_raw with (edge := edge) (old := oldhigh);
        eauto; try lia. split; assumption.
    + split.
      * exists output. split; [exact Houtput|]. unfold output.
        rewrite <- decode_word8_projection, put_byte_projection by lia.
        apply decode_word8_projection.
      * split.
        -- intros old HL. assert (old = oldhigh) by congruence. subst old.
           exists output. split; [exact Houtput|]. apply put_byte_prefix; lia.
        -- split.
           ++ split.
              ** erewrite Mem.load_store_other; [|exact SF|right; left; change (base + 8 <= base + 8); lia].
                 erewrite word_store_preserves_frame_load; [exact HF|exact HD|lia|change (base + 8 <= base + 16); lia|exact SW].
              ** exact (Mem.load_store_same _ _ _ _ _ _ SF).
           ++ split.
              ** intros chunk b ofs Hbf Hbw.
                 erewrite Mem.load_store_other; [|exact SF|cbn; lia].
                 eapply Mem.load_store_other; [exact SW|cbn; lia].
              ** split.
                 --- intros b ofs kind p HP. eauto using Mem.perm_store_1.
                 --- intros b HV. eauto using Mem.store_valid_block_1.
  - destruct (write_frame_at_crossing m bf base bw edge cursor ltac:(lia) HFrame)
      as [HAL [PL [oldlow HL]]].
    pose proof (write_frame_at_crossing_separate m bf base bw edge cursor ltac:(lia) HFrame) as HDL.
    set (k := write_word_shift cursor).
    destruct (Mem.valid_access_store m Mint64 bw (write_word_address edge cursor)
        (Vlong (crossing_high k oldhigh x)) PH) as [mh SH].
    assert (PDh : Mem.valid_access mh Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mh Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor - k))) PDh) as [mo SO].
    assert (PLo : Mem.valid_access mo Mint64 bw (write_word_address edge cursor - 8) Writable)
      by (eauto using Mem.store_valid_access_1).
    destruct (Mem.valid_access_store mo Mint64 bw (write_word_address edge cursor - 8)
        (Vlong (crossing_low k x)) PLo) as [mw SW].
    assert (PDw : Mem.valid_access mw Mint64 bf (base + 8) Writable)
      by (eauto using Mem.store_valid_access_1).
    destruct (Mem.valid_access_store mw Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor - 8))) PDw) as [mf SF].
    assert (Hhigh : Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong (crossing_high k oldhigh x))).
    { erewrite frame_store_preserves_word_load; [|eassumption|exact SF].
      erewrite Mem.load_store_other; [|exact SW|right; right; cbn; lia].
      erewrite frame_store_preserves_word_load; [|eassumption|exact SO].
      exact (Mem.load_store_same _ _ _ _ _ _ SH). }
    assert (Hlow : Mem.load Mint64 mf bw (write_word_address edge cursor - 8) = Some (Vlong (crossing_low k x))).
    { erewrite frame_store_preserves_word_load; [|eassumption|exact SF]. exact (Mem.load_store_same _ _ _ _ _ _ SW). }
    exists mf. split.
    + eapply eval_write8_layout_crossing_raw with (edge := edge) (k := k)
        (oldhigh := oldhigh) (oldlow := oldlow); eauto; try (unfold k; lia).
      * split; assumption.
      * erewrite word_store_preserves_frame_load; [exact HO|exact HD|lia|change (base + 8 + 8 <= base + 16); lia|exact SH].
      * erewrite frame_store_preserves_word_load; [|eassumption|exact SO].
        erewrite Mem.load_store_other; [exact HL|exact SH|right; left; cbn; lia].
      * erewrite word_store_preserves_frame_load; [|exact HDL|lia|change (base + 8 + 8 <= base + 16); lia|exact SW]. exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + split.
      * exists (crossing_high k oldhigh x), (crossing_low k x).
        split; [exact Hhigh|]. split; [exact Hlow|]. apply crossing_byte_decode; unfold k; lia.
      * split.
        -- intros old HH'. assert (old = oldhigh) by congruence. subst old.
           exists (crossing_high k oldhigh x). split; [exact Hhigh|]. apply crossing_high_prefix; unfold k; lia.
        -- split.
           ++ split.
              ** erewrite Mem.load_store_other; [|exact SF|right; left; change (base + 8 <= base + 8); lia].
                 erewrite word_store_preserves_frame_load; [|exact HDL|lia|change (base + 8 <= base + 16); lia|exact SW].
                 erewrite Mem.load_store_other; [|exact SO|right; left; change (base + 8 <= base + 8); lia].
                 erewrite word_store_preserves_frame_load; [exact HF|exact HD|lia|change (base + 8 <= base + 16); lia|exact SH].
              ** exact (Mem.load_store_same _ _ _ _ _ _ SF).
           ++ split.
              ** intros chunk b ofs Hbf Hbw.
                 erewrite Mem.load_store_other; [|exact SF|cbn; lia].
                 erewrite Mem.load_store_other; [|exact SW|cbn; lia].
                 erewrite Mem.load_store_other; [|exact SO|cbn; lia].
                 eapply Mem.load_store_other; [exact SH|cbn; lia].
              ** split.
                 --- intros b ofs kind p HP. eauto 8 using Mem.perm_store_1.
                 --- intros b HV. eauto 8 using Mem.store_valid_block_1.
Qed.
