(** Logical cell observations of the two plain-[memcpy] paths of copyBits for
    counts up to 64, and their wrapper contracts (conditional on the explicit
    [memcpy_model]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_context_separated C.jet_frame_spec.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_right C.jet_copyBits_short_word.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_copyBits_short_cells.
Require Import C.jet_copyBits_aligned_short C.jet_copyBits_aligned_crossing.
Require Import C.jet_copyBits_two_words_left_cells C.jet_copyBits_separation C.jet_copyBits_two_words_right_full_cells.
Require Import C.jet_memcpy_model C.jet_copyBits_memcpy_helper.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

(** * Both frames aligned *)

Lemma copy_memcpy_aligned_output_bit m mf bi edge rc bw outedge cursor n source j bit :
  rc mod 64 = 0 -> cursor mod 64 = 0 -> 0 < n <= 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) = Some (Vlong source) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hrz Hcz Hn HC Hj Hsource Hresult [_ [_ [w [HW Hb]]]].
  pose proof (Z.div_mod rc 64 ltac:(lia)) as Hdm.
  destruct (div_mod_64 (rc + j) (rc / 64) j) as [Hqr Hmr]; [lia|lia|].
  destruct (copy_aligned_write_position cursor j Hcz ltac:(lia)) as [Hqw Hmw].
  rewrite Hqr in HW. rewrite Hsource in HW. injection HW as <-.
  split; [lia|]. exists source. rewrite Hqw, Hmw. split; [exact Hresult|].
  rewrite Hmr in Hb. exact Hb.
Qed.

Lemma copy_memcpy_aligned_output_cells m mf bi edge rc bw outedge cursor n source cells :
  rc mod 64 = 0 -> cursor mod 64 = 0 -> 0 < n <= 64 -> n <= cursor -> n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) = Some (Vlong source) ->
  frame_input_cells_at m bi edge rc cells ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hrz Hcz Hn HC Hlen Hsource Hresult Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_memcpy_aligned_output_bit with (rc := rc) (cursor := cursor); try eassumption; lia.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_memcpy_aligned_output_bit with (rc := rc) (cursor := cursor); try eassumption; lia.
Qed.

Theorem eval_copyBits_memcpy_aligned_layout (Hmodel : memcpy_model) m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  rc mod 64 = 0 -> cursor mod 64 = 0 -> 0 < n <= 64 ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  frame_input_cells_at m bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (write_word_address outedge cursor) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HF Hwrite Hlen Hrz Hcz Hn Hsep Hinput.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (eval_copy_helper_memcpy_aligned Hmodel m bd base bs sbase bi edge rc bw outedge cursor n source
    HS HB HF HW HR ltac:(lia) HE HO ltac:(lia) Hrz Hcz Hn ltac:(lia) Hbd Hsep Hsource PW)
    as [mi [Hcall [Hword [Hfields [Houtside [Hperm Hvalid]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hresult : Mem.load Mint64 mf bw (write_word_address outedge cursor) = Some (Vlong source)).
  { rewrite HcursorOutside; [exact Hword|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_memcpy_aligned_output_cells with (rc := rc) (cursor := cursor); try eassumption; lia.
  - split; [eapply copy_aligned_written_prefix; eassumption|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.

(** * Equal initial shifts with a partial destination word *)

Lemma copy_memcpy_equal_output_bit m mf bi edge rc bw outedge cursor n old source next j bit :
  0 < cursor mod 64 -> cursor mod 64 = 64 - rc mod 64 -> cursor mod 64 < n <= 64 ->
  n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) = Some (Vlong next) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hpartial Hss Hn HC Hj Hsource Hnext Hhead Hlow Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (zlt j (cursor mod 64)) as [Hfirst|Hsecond].
  - assert (HshortHead : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
        Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source))).
    { unfold copy_short_value. rewrite zlt_false by lia; exact Hhead. }
    eapply copy_short_output_bit with (n := cursor mod 64); try eassumption; lia.
  - destruct Hinput as [_ [_ [w [HW Hb]]]].
    destruct (copy_partial_cross_write_position cursor j Hpartial ltac:(lia)) as [Hqw Hmw].
    destruct (copy_crossing_read_position rc j ltac:(lia)) as [Hqr Hmr].
    split; [lia|]. exists next.
    rewrite Hqw, Hmw. split.
    + replace (outedge + 8 * ((cursor - 1) / 64 - 1)) with (write_word_address outedge cursor - 8)
        by (unfold write_word_address; lia). exact Hlow.
    + rewrite Hqr in HW.
      replace (edge - 8 * (1 + (rc / 64 + 1))) with (edge - 8 * (2 + rc / 64)) in HW by lia.
      rewrite Hnext in HW. injection HW as <-. rewrite Hmr in Hb.
      replace (63 - (j - cursor mod 64)) with (63 - (j - (64 - rc mod 64))) by lia.
      exact Hb.
Qed.

Lemma copy_memcpy_equal_output_cells m mf bi edge rc bw outedge cursor n old source next cells :
  0 < cursor mod 64 -> cursor mod 64 = 64 - rc mod 64 -> cursor mod 64 < n <= 64 ->
  n <= cursor -> n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) = Some (Vlong next) ->
  frame_input_cells_at m bi edge rc cells -> frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hpartial Hss Hn HC Hlen Hsource Hnext Hhead Hlow Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_memcpy_equal_output_bit with (rc := rc) (cursor := cursor); try eassumption; lia.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_memcpy_equal_output_bit with (rc := rc) (cursor := cursor); try eassumption; lia.
Qed.

Theorem eval_copyBits_memcpy_equal_layout (Hmodel : memcpy_model) m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < cursor mod 64 -> cursor mod 64 = 64 - rc mod 64 -> cursor mod 64 < n <= 64 ->
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
  intros HS HF Hwrite Hlen Hpartial Hss Hn Hsep Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (Hwords (cursor mod 64) ltac:(lia)) as [Hlow0 [Hlowmax [PWlow Hlowold]]].
  rewrite copy_partial_cross_write_address in Hlow0, Hlowmax, PWlow by exact Hpartial.
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (copy_crossing_input_word m bi edge rc n cells ltac:(lia) ltac:(lia) Hlen Hinput)
    as [HE2 [next Hnext]].
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n 0 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsephead.
  rewrite Z.add_0_r, Z.sub_0_r in Hsephead.
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n (64 - rc mod 64) 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsepnext.
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n (64 - rc mod 64) (cursor mod 64) Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsepnextlow.
  destruct (copy_crossing_read_position rc (64 - rc mod 64) ltac:(lia)) as [Hq _].
  rewrite Hq, Z.sub_0_r in Hsepnext.
  rewrite Hq, copy_partial_aligned_write_address in Hsepnextlow by exact Hpartial.
  replace (1 + (rc / 64 + 1)) with (2 + rc / 64) in Hsepnext, Hsepnextlow by lia.
  destruct (eval_copy_helper_memcpy_equal Hmodel m bd base bs sbase bi edge rc bw outedge cursor n old source next
    HS HB HF HW HR ltac:(lia) HE2 HO ltac:(lia) Hpartial Hss Hn ltac:(lia) Hbd
    Hsephead Hsepnext Hsepnextlow Hsource Hnext Hold PW PWlow)
    as [mi [Hcall [Hhead [Hlow [Hfields [Houtside [Hperm Hvalid]]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hheadf : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_right_value (64 - rc mod 64) (cursor mod 64) old source))).
  { rewrite HcursorOutside; [exact Hhead|left; congruence]. }
  assert (Hlowf : Mem.load Mint64 mf bw (write_word_address outedge cursor - 8) = Some (Vlong next)).
  { rewrite HcursorOutside; [exact Hlow|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_memcpy_equal_output_cells with (rc := rc) (cursor := cursor); try eassumption; try lia.
  - split.
    + eapply copy_short_written_prefix with (rc := rc) (old := old) (source := source); try eassumption.
      unfold copy_short_value. rewrite zlt_false by lia; exact Hheadf.
    + split; [exact Hfieldsf|]. split.
      * intros chunk b ofs Hcursor HwordOutside.
        rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
      * split.
        -- intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
        -- intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
