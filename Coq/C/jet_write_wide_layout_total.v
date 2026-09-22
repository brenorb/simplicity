(** Total 16/32/64-bit writes from initial frame permissions, including crossings. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_word_slice C.jet_output_slice C.jet_write_wide_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_write_wide_layout s m bf base bw edge cursor x :
  write_frame_at m bf base bw edge cursor (wide_bits s) ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef /\
    slice_output_at (wide_bits s) mf bw edge cursor (Int64.zero_ext (wide_bits s) x) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - wide_bits s) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (slice_write_low (wide_bits s) edge cursor) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame. pose proof (wide_bits_bounds s) as HNbound.
  pose proof HFrame as [HB [[HF HO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bf base bw edge cursor (wide_bits s) ltac:(lia) HFrame)
    as [HA0 [HA [PH [oldhigh HH]]]].
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  unfold slice_output_at, slice_write_low.
  destruct (Z_le_dec (wide_bits s) (write_word_shift cursor)) as [HN | HX].
  - set (output := put_slice (wide_bits s) (write_word_shift cursor) oldhigh x).
    destruct (Mem.valid_access_store m Mint64 bw (write_word_address edge cursor) (Vlong output) PH)
      as [mw SW].
    assert (PDw : Mem.valid_access mw Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mw Mint64 bf (base + 8) (Vlong (Int64.repr (cursor - wide_bits s))) PDw)
      as [mf SF].
    assert (Houtput : Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong output)).
    { erewrite Mem.load_store_other; [|exact SF|auto]. exact (Mem.load_store_same _ _ _ _ _ _ SW). }
    exists mf. split.
    + eapply eval_write_wide_non_crossing_raw with (edge := edge) (old := oldhigh);
        eauto; try lia. split; assumption.
    + split.
      * exists output. split; [exact Houtput|]. unfold output.
        apply put_slice_projection; lia.
      * split.
        -- intros old HL. assert (old = oldhigh) by congruence. subst old.
           exists output. split; [exact Houtput|]. apply put_slice_prefix; lia.
        -- split.
           ++ split.
              ** erewrite Mem.load_store_other; [|exact SF|right; left; change (base + 8 <= base + 8); lia].
                 erewrite Mem.load_store_other; [exact HF|exact SW|auto].
              ** exact (Mem.load_store_same _ _ _ _ _ _ SF).
           ++ split.
              ** intros chunk b ofs Hbf Hbw.
                 erewrite Mem.load_store_other; [|exact SF|cbn; lia].
                 eapply Mem.load_store_other; [exact SW|cbn; lia].
              ** split.
                 --- intros b ofs kind p HP. eauto using Mem.perm_store_1.
                 --- intros b HV. eauto using Mem.store_valid_block_1.
  - destruct (write_frame_at_slice_crossing (wide_bits s) m bf base bw edge cursor ltac:(lia) HFrame)
      as [HAL [PL [oldlow HL]]].
    set (k := write_word_shift cursor).
    destruct (Mem.valid_access_store m Mint64 bw (write_word_address edge cursor)
        (Vlong (slice_high (wide_bits s) k oldhigh x)) PH) as [mh SH].
    assert (PDh : Mem.valid_access mh Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mh Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor - k))) PDh) as [mo SO].
    assert (PLo : Mem.valid_access mo Mint64 bw (write_word_address edge cursor - 8) Writable)
      by (eauto using Mem.store_valid_access_1).
    destruct (Mem.valid_access_store mo Mint64 bw (write_word_address edge cursor - 8)
        (Vlong (slice_low (wide_bits s) k x)) PLo) as [mw SW].
    assert (PDw : Mem.valid_access mw Mint64 bf (base + 8) Writable)
      by (eauto using Mem.store_valid_access_1).
    destruct (Mem.valid_access_store mw Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor - wide_bits s))) PDw) as [mf SF].
    assert (Hhigh : Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong (slice_high (wide_bits s) k oldhigh x))).
    { erewrite Mem.load_store_other; [|exact SF|auto].
      erewrite Mem.load_store_other; [|exact SW|right; right; cbn; lia].
      erewrite Mem.load_store_other; [|exact SO|auto].
      exact (Mem.load_store_same _ _ _ _ _ _ SH). }
    assert (Hlow : Mem.load Mint64 mf bw (write_word_address edge cursor - 8) = Some (Vlong (slice_low (wide_bits s) k x))).
    { erewrite Mem.load_store_other; [|exact SF|auto]. exact (Mem.load_store_same _ _ _ _ _ _ SW). }
    exists mf. split.
    + eapply eval_write_wide_crossing_raw with (edge := edge) (k := k)
        (oldhigh := oldhigh) (oldlow := oldlow); eauto; try (unfold k; lia).
      * split; assumption.
      * erewrite Mem.load_store_other; [exact HO|exact SH|auto].
      * erewrite Mem.load_store_other; [|exact SO|auto].
        erewrite Mem.load_store_other; [exact HL|exact SH|right; left; cbn; lia].
      * erewrite Mem.load_store_other; [|exact SW|auto]. exact (Mem.load_store_same _ _ _ _ _ _ SO).
    + split.
      * exists (slice_high (wide_bits s) k oldhigh x), (slice_low (wide_bits s) k x).
        split; [exact Hhigh|]. split; [exact Hlow|]. apply crossing_slice_projection; unfold k; lia.
      * split.
        -- intros old HH'. assert (old = oldhigh) by congruence. subst old.
           exists (slice_high (wide_bits s) k oldhigh x). split; [exact Hhigh|]. apply slice_high_prefix; unfold k; lia.
        -- split.
           ++ split.
              ** erewrite Mem.load_store_other; [|exact SF|right; left; change (base + 8 <= base + 8); lia].
                 erewrite Mem.load_store_other; [|exact SW|auto].
                 erewrite Mem.load_store_other; [|exact SO|right; left; change (base + 8 <= base + 8); lia].
                 erewrite Mem.load_store_other; [exact HF|exact SH|auto].
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
