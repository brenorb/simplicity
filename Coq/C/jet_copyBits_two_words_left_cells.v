(** Logical cells for the actual copy crossing both word boundaries when
    src_shift < dst_shift. The initial contract derives word separation from
    the represented caller's buffer predicate, not extra layout assumptions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep C.jet_context_separated C.jet_frame_spec.
Require Import C.jet_copyBits_exec C.jet_copyBits_partial_crossing C.jet_copyBits_loop_exec.
Require Import C.jet_copyBits_short_cells C.jet_copyBits_aligned_short C.jet_copyBits_aligned_crossing.
Require Import C.jet_copyBits_partial_crossing_cells C.jet_copyBits_separation C.jet_copyBits_two_words_left.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_partial_cross_write_position cursor j :
  0 < cursor mod 64 -> cursor mod 64 <= j < cursor mod 64 + 64 ->
  (cursor - 1 - j) / 64 = (cursor - 1) / 64 - 1 /\
  (cursor - 1 - j) mod 64 = 63 - (j - cursor mod 64).
Proof.
  intros Hpartial Hj. pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)).
  pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64) (cursor mod 64 - 1)) as [Hq0 _]; [lia|lia|].
  destruct (div_mod_64 (cursor - 1 - j) (cursor / 64 - 1)
    (63 - (j - cursor mod 64))) as [Hq Hm]; [lia|lia|].
  split; congruence.
Qed.

Lemma copy_partial_cross_write_address edge cursor :
  0 < cursor mod 64 ->
  write_cell_address edge cursor (cursor mod 64) = write_word_address edge cursor - 8.
Proof.
  intros Hpartial. destruct (copy_partial_cross_write_position cursor (cursor mod 64)
    Hpartial ltac:(lia)) as [Hq _].
  unfold write_cell_address, write_word_address. rewrite Hq; lia.
Qed.

Lemma copy_two_left_output_bit m mf bi edge rc bw outedge cursor n old source next j bit :
  64 - rc mod 64 < cursor mod 64 -> cursor mod 64 < n <= 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
    Some (Vlong (copy_loop_value (64 - (cursor mod 64 - (64 - rc mod 64))) next)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hshift Hn HC Hj Hsource Hnext Hhead Hlow Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (zlt j (cursor mod 64)) as [Hfirst|Hsecond].
  - eapply copy_partial_cross_output_bit with (n := cursor mod 64); try eassumption; lia.
  - destruct Hinput as [_ [_ [w [HW Hb]]]].
    destruct (copy_crossing_read_position rc j ltac:(lia)) as [Hqr Hmr].
    rewrite Hqr in HW.
    replace (edge - 8 * (1 + (rc / 64 + 1))) with (edge - 8 * (2 + rc / 64)) in HW by lia.
    rewrite Hnext in HW. injection HW as <-. rewrite Hmr in Hb.
    destruct (copy_partial_cross_write_position cursor j ltac:(lia) ltac:(lia)) as [Hqw Hmw].
    split; [lia|]. exists (copy_loop_value (64 - (cursor mod 64 - (64 - rc mod 64))) next).
    rewrite Hqw, Hmw. split.
    + replace (outedge + 8 * ((cursor - 1) / 64 - 1)) with (write_word_address outedge cursor - 8)
        by (unfold write_word_address; lia). exact Hlow.
    + rewrite copy_loop_copied_bit with (n := n - cursor mod 64) by lia.
      replace (64 - (cursor mod 64 - (64 - rc mod 64)) - 1 - (j - cursor mod 64))
        with (63 - (j - (64 - rc mod 64))) by lia. exact Hb.
Qed.

Lemma copy_two_left_output_cells m mf bi edge rc bw outedge cursor n old source next cells :
  64 - rc mod 64 < cursor mod 64 -> cursor mod 64 < n <= 64 -> n <= cursor ->
  n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
    Some (Vlong (copy_loop_value (64 - (cursor mod 64 - (64 - rc mod 64))) next)) ->
  frame_input_cells_at m bi edge rc cells -> frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hshift Hn HC Hlen Hsource Hnext Hhead Hlow Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_two_left_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_two_left_output_bit; eassumption.
Qed.

Theorem eval_copyBits_two_left_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  64 - rc mod 64 < cursor mod 64 -> cursor mod 64 < n <= 64 ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc n ->
  frame_input_cells_at m bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (write_word_address outedge cursor - 8) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HF Hwrite Hlen Hshift Hn Hsep Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (Hwords (cursor mod 64) ltac:(lia)) as [Hlow0 [Hlowmax [PWlow Hlowold]]].
  rewrite copy_partial_cross_write_address in Hlow0, Hlowmax, PWlow by lia.
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (copy_crossing_input_word m bi edge rc n cells ltac:(lia) ltac:(lia) Hlen Hinput)
    as [HE2 [next Hnext]].
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n 0 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsephead.
  rewrite Z.add_0_r, Z.sub_0_r in Hsephead.
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n (64 - rc mod 64) 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsepnext.
  destruct (copy_crossing_read_position rc (64 - rc mod 64) ltac:(lia)) as [Hq _].
  rewrite Hq, Z.sub_0_r in Hsepnext.
  replace (1 + (rc / 64 + 1)) with (2 + rc / 64) in Hsepnext by lia.
  destruct (eval_copy_helper_two_left m bd base bs sbase bi edge rc bw outedge cursor n old source next
    HS HB HF HW HR ltac:(lia) HE2 HO ltac:(lia) Hshift Hn ltac:(lia) Hbd
    Hsephead Hsepnext Hsource Hnext Hold PW PWlow)
    as [mi [Hcall [Hhead [Hlow [Hfields [Houtside [Hperm Hvalid]]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hheadf : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next))).
  { rewrite HcursorOutside; [exact Hhead|left; congruence]. }
  assert (Hlowf : Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
      Some (Vlong (copy_loop_value (64 - (cursor mod 64 - (64 - rc mod 64))) next))).
  { rewrite HcursorOutside; [exact Hlow|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_two_left_output_cells; try eassumption; lia.
  - split; [eapply copy_partial_cross_written_prefix; eassumption|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
