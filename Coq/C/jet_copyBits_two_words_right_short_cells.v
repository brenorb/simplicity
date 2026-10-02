(** Logical wrapper contract for destination-only word crossings. The source
    may initially be aligned; no next-source-word load or memcpy is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_context_separated C.jet_frame_spec.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_right C.jet_copyBits_short_word C.jet_copyBits_loop_exec.
Require Import C.jet_copyBits_short_cells C.jet_copyBits_aligned_short C.jet_copyBits_separation.
Require Import C.jet_copyBits_two_words_left_cells C.jet_copyBits_two_words_right_short.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_two_right_short_output_bit m mf bi edge rc bw outedge cursor n old source j bit :
  0 < cursor mod 64 -> cursor mod 64 < n <= 64 - rc mod 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
    Some (Vlong (copy_loop_value (64 - rc mod 64 - cursor mod 64) source)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hpartial Hn HC Hj Hsource Hhead Hlow Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (zlt j (cursor mod 64)) as [Hfirst|Hsecond].
  - assert (HshortHead : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
        Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source))).
    { unfold copy_short_value. rewrite zlt_false by lia; exact Hhead. }
    eapply copy_short_output_bit with (n := cursor mod 64); try eassumption; lia.
  - destruct Hinput as [_ [_ [w [HW Hb]]]].
    destruct (copy_short_read_position rc j ltac:(lia)) as [Hqr Hmr].
    rewrite Hqr in HW. rewrite Hsource in HW. injection HW as <-. rewrite Hmr in Hb.
    destruct (copy_partial_cross_write_position cursor j Hpartial ltac:(lia)) as [Hqw Hmw].
    split; [lia|]. exists (copy_loop_value (64 - rc mod 64 - cursor mod 64) source).
    rewrite Hqw, Hmw. split.
    + replace (outedge + 8 * ((cursor - 1) / 64 - 1)) with (write_word_address outedge cursor - 8)
        by (unfold write_word_address; lia). exact Hlow.
    + rewrite copy_loop_copied_bit with (n := n - cursor mod 64) by lia.
      replace (64 - rc mod 64 - cursor mod 64 - 1 - (j - cursor mod 64))
        with (63 - (rc mod 64 + j)) by lia. exact Hb.
Qed.

Lemma copy_two_right_short_output_cells m mf bi edge rc bw outedge cursor n old source cells :
  0 < cursor mod 64 -> cursor mod 64 < n <= 64 - rc mod 64 -> n <= cursor ->
  n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
    Some (Vlong (copy_loop_value (64 - rc mod 64 - cursor mod 64) source)) ->
  frame_input_cells_at m bi edge rc cells -> frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hpartial Hn HC Hlen Hsource Hhead Hlow Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_two_right_short_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_two_right_short_output_bit; eassumption.
Qed.

Theorem eval_copyBits_two_right_short_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < cursor mod 64 -> cursor mod 64 < n <= 64 - rc mod 64 ->
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
  intros HS HF Hwrite Hlen Hpartial Hn Hsep Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (Hwords (cursor mod 64) ltac:(lia)) as [Hlow0 [Hlowmax [PWlow Hlowold]]].
  rewrite copy_partial_cross_write_address in Hlow0, Hlowmax, PWlow by exact Hpartial.
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n 0 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsephead.
  rewrite Z.add_0_r, Z.sub_0_r in Hsephead.
  destruct (eval_copy_helper_two_right_short m bd base bs sbase bi edge rc bw outedge cursor n old source
    HS HB HF HW HR ltac:(lia) HE HO ltac:(lia) Hpartial Hn ltac:(lia) Hbd
    Hsephead Hsource Hold PW PWlow)
    as [mi [Hcall [Hhead [Hlow [Hfields [Houtside [Hperm Hvalid]]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hheadf : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source))).
  { rewrite HcursorOutside; [|left; congruence].
    unfold copy_short_value. rewrite zlt_false by lia; exact Hhead. }
  assert (Hlowf : Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) =
      Some (Vlong (copy_loop_value (64 - rc mod 64 - cursor mod 64) source))).
  { rewrite HcursorOutside; [exact Hlow|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_two_right_short_output_cells; try eassumption; try lia.
    unfold copy_short_value in Hheadf. rewrite zlt_false in Hheadf by lia; exact Hheadf.
  - split; [eapply copy_short_written_prefix; eassumption|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
