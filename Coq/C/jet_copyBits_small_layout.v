(** Uniform initial-only frame contract for positive copies up to 64 bits,
    excluding the two aligned paths proved separately through [copyWords].
    This is NOT a complete copyBits or public jet equivalence theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_context_separated.
Require Import C.jet_copyBits_short_cells C.jet_copyBits_aligned_crossing.
Require Import C.jet_copyBits_partial_crossing_cells C.jet_copyBits_separation.
Require Import C.jet_copyBits_two_words_left_cells C.jet_copyBits_two_words_right_short_cells.
Require Import C.jet_copyBits_two_words_right_full_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition copy_small_memcpy_case rc cursor n : Prop :=
  (cursor mod 64 = 0 /\ rc mod 64 = 0) \/
  (0 < cursor mod 64 /\ 64 - rc mod 64 = cursor mod 64 /\ cursor mod 64 < n).

Lemma copy_small_aligned_low edge cursor n :
  cursor mod 64 = 0 -> 0 < n <= 64 ->
  edge + 8 * ((cursor - n) / 64) = write_word_address edge cursor.
Proof.
  intros Hz Hn. pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64 - 1) 63) as [Hq0 _]; [lia|lia|].
  destruct (div_mod_64 (cursor - n) (cursor / 64 - 1) (64 - n)) as [Hq _]; [lia|lia|].
  unfold write_word_address. rewrite Hq0, Hq; reflexivity.
Qed.

Lemma copy_small_partial_low edge cursor n :
  0 < cursor mod 64 -> 0 < n <= cursor mod 64 ->
  edge + 8 * ((cursor - n) / 64) = write_word_address edge cursor.
Proof.
  intros Hpartial Hn. pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)).
  pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64) (cursor mod 64 - 1)) as [Hq0 _]; [lia|lia|].
  destruct (div_mod_64 (cursor - n) (cursor / 64) (cursor mod 64 - n)) as [Hq _]; [lia|lia|].
  unfold write_word_address. rewrite Hq0, Hq; reflexivity.
Qed.

Lemma copy_small_crossing_low edge cursor n :
  0 < cursor mod 64 -> cursor mod 64 < n <= 64 ->
  edge + 8 * ((cursor - n) / 64) = write_word_address edge cursor - 8.
Proof.
  intros Hpartial Hn. pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)).
  pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64) (cursor mod 64 - 1)) as [Hq0 _]; [lia|lia|].
  destruct (div_mod_64 (cursor - n) (cursor / 64 - 1) (cursor mod 64 - n + 64))
    as [Hq _]; [lia|lia|].
  unfold write_word_address. rewrite Hq0, Hq; lia.
Qed.

Theorem eval_copyBits_small_no_memcpy_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < n <= 64 -> ~ copy_small_memcpy_case rc cursor n ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc n ->
  frame_input_cells_at m bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (outedge + 8 * ((cursor - n) / 64)) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HF Hwrite Hlen Hn Hno Hsep Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  pose proof Hwrite as HWC. destruct HWC as [_ [_ [_ [Hcapacity _]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput) as [HR Hrest].
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n 0 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsephead.
  rewrite Z.add_0_r, Z.sub_0_r in Hsephead.
  assert (Hsepnext : 64 - rc mod 64 < n ->
    bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)).
  { intros Hcross. pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n
      (64 - rc mod 64) 0 Hsep ltac:(lia) ltac:(lia) ltac:(lia)) as Hword.
    destruct (copy_crossing_read_position rc (64 - rc mod 64) ltac:(lia)) as [Hq _].
    rewrite Hq, Z.sub_0_r in Hword.
    replace (1 + (rc / 64 + 1)) with (2 + rc / 64) in Hword by lia; exact Hword. }
  destruct (Z.eq_dec (cursor mod 64) 0) as [Hz|Hnz].
  - assert (Hsrc : 0 < rc mod 64).
    { destruct (Z.eq_dec (rc mod 64) 0) as [Hrz|Hrnz]; [|lia].
      exfalso. apply Hno. left; split; assumption. }
    rewrite (copy_small_aligned_low outedge cursor n Hz Hn).
    eapply eval_copyBits_aligned_partial_source_layout; eassumption.
  - assert (Hpartial : 0 < cursor mod 64) by lia.
    destruct (Z_le_dec n (cursor mod 64)) as [Hfits|Hcontinues].
    + rewrite (copy_small_partial_low outedge cursor n Hpartial ltac:(lia)).
      eapply eval_copyBits_partial_word_layout; try eassumption; lia.
    + rewrite (copy_small_crossing_low outedge cursor n Hpartial ltac:(lia)).
      destruct (Z_lt_dec (64 - rc mod 64) (cursor mod 64)) as [Hleft|Hright].
      * eapply eval_copyBits_two_left_layout; try eassumption; lia.
      * destruct (Z_le_dec n (64 - rc mod 64)) as [Hshort|Hfull].
        -- eapply eval_copyBits_two_right_short_layout; try eassumption; lia.
        -- assert (Hshift : cursor mod 64 < 64 - rc mod 64).
           { destruct (Z.eq_dec (64 - rc mod 64) (cursor mod 64)) as [Heq|Hneq]; [|lia].
             exfalso. apply Hno. right; repeat split; assumption || lia. }
           eapply eval_copyBits_two_right_full_layout; try eassumption; lia.
Qed.
