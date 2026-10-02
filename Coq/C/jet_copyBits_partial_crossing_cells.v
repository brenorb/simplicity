(** Initial-only logical contract for a source crossing within the partial
    destination word. This composes the actual helper and cursor wrapper;
    it is not yet a complete projection-jet equivalence theorem. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_copyBits_exec.
Require Import C.jet_copyBits_helper_exec C.jet_copyBits_helper_right C.jet_copyBits_short_word.
Require Import C.jet_copyBits_short_cells C.jet_copyBits_aligned_crossing.
Require Import C.jet_copyBits_partial_crossing.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_partial_cross_value_bits ss ds old source next i :
  1 <= ss /\ ss < ds <= 63 -> 0 <= i < 64 ->
  Int64.testbit (copy_partial_cross_value ss ds old source next) i =
    if zlt i (ds - ss) then Int64.testbit next (i + (64 - (ds - ss)))
    else if zlt i ds then Int64.testbit source (i - (ds - ss))
    else Int64.testbit old i.
Proof.
  intros Hr Hi. unfold copy_partial_cross_value.
  rewrite copy_right_value_bits by lia. destruct (zlt i (ds - ss)); [reflexivity|].
  rewrite copy_left_value_bits by lia. rewrite zlt_false by lia; reflexivity.
Qed.

Lemma copy_partial_cross_copied_bit ss ds n old source next j :
  1 <= ss /\ ss < ds <= 63 -> ss < n <= ds -> 0 <= j < n ->
  Int64.testbit (copy_partial_cross_value ss ds old source next) (ds - 1 - j) =
    if zlt j ss then Int64.testbit source (ss - 1 - j)
    else Int64.testbit next (63 - (j - ss)).
Proof.
  intros Hr Hn Hj. rewrite copy_partial_cross_value_bits by lia.
  destruct (zlt j ss).
  - rewrite zlt_false by lia. rewrite zlt_true by lia. f_equal; lia.
  - rewrite zlt_true by lia. f_equal; lia.
Qed.

Lemma copy_partial_cross_existing_bit ss ds old source next i :
  1 <= ss /\ ss < ds <= 63 -> ds <= i < 64 ->
  Int64.testbit (copy_partial_cross_value ss ds old source next) i = Int64.testbit old i.
Proof.
  intros Hr Hi. rewrite copy_partial_cross_value_bits by lia.
  rewrite !zlt_false by lia; reflexivity.
Qed.

Lemma copy_partial_cross_output_bit m mf bi edge rc bw outedge cursor n old source next j bit :
  64 - rc mod 64 < n <= cursor mod 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hn HC Hj Hsource Hnext Hresult [_ [_ [w [HW Hb]]]].
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (copy_short_write_position cursor j ltac:(lia) ltac:(lia)) as [Hqw Hmw].
  split; [lia|]. exists (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next).
  rewrite Hqw, Hmw. split; [exact Hresult|].
  rewrite copy_partial_cross_copied_bit with (n := n) by lia.
  destruct (zlt j (64 - rc mod 64)) as [Hfirst|Hsecond].
  - destruct (copy_short_read_position rc j ltac:(lia)) as [Hqr Hmr].
    rewrite Hqr in HW. rewrite Hsource in HW. injection HW as <-.
    rewrite Hmr in Hb. replace (63 - (rc mod 64 + j)) with (64 - rc mod 64 - 1 - j) in Hb by lia.
    exact Hb.
  - destruct (copy_crossing_read_position rc j ltac:(lia)) as [Hqr Hmr].
    rewrite Hqr in HW.
    replace (edge - 8 * (1 + (rc / 64 + 1))) with (edge - 8 * (2 + rc / 64)) in HW by lia.
    rewrite Hnext in HW. injection HW as <-. rewrite Hmr in Hb. exact Hb.
Qed.

Lemma copy_partial_cross_output_cells m mf bi edge rc bw outedge cursor n old source next cells :
  64 - rc mod 64 < n <= cursor mod 64 -> n <= cursor -> n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) ->
  frame_input_cells_at m bi edge rc cells ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hn HC Hlen Hsource Hnext Hresult Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_partial_cross_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_partial_cross_output_bit; eassumption.
Qed.

Lemma copy_partial_cross_written_prefix m mf bw edge cursor rc old source next :
  64 - rc mod 64 < cursor mod 64 ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
  Mem.load Mint64 mf bw (write_word_address edge cursor) =
    Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next)) ->
  write_prefix_at m mf bw edge cursor.
Proof.
  intros Hpartial Hold Hresult old' Hold'. rewrite Hold in Hold'. injection Hold' as <-.
  exists (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next).
  split; [exact Hresult|]. intros i Hi [Hlow|Hhigh]; [lia|].
  rewrite copy_short_write_shift in Hhigh by
    (pose proof (Z.mod_pos_bound rc 64 ltac:(lia)); lia).
  apply copy_partial_cross_existing_bit; pose proof (Z.mod_pos_bound rc 64 ltac:(lia));
    pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia.
Qed.

Theorem eval_copyBits_partial_cross_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  64 - rc mod 64 < n <= cursor mod 64 ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  (bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)) ->
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
  intros HS HF Hwrite Hlen Hn Hsep Hsepnext Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (copy_crossing_input_word m bi edge rc n cells ltac:(lia) ltac:(lia) Hlen Hinput)
    as [HE2 [next Hnext]].
  destruct (eval_copy_helper_partial_cross m bd base bs sbase bi edge rc bw outedge cursor n old source next
    HS HB HF HW HR ltac:(lia) HE2 HO ltac:(lia) Hn Hbd Hsep Hsepnext Hsource Hnext Hold PW)
    as [mi [Hcall [Hword [Hfields [Houtside [Hperm Hvalid]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hresult : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_partial_cross_value (64 - rc mod 64) (cursor mod 64) old source next))).
  { rewrite HcursorOutside; [exact Hword|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_partial_cross_output_cells; try eassumption; lia.
  - split; [eapply copy_partial_cross_written_prefix; try eassumption; lia|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.

(** Unified initial-only contract for every positive copy fitting in the
    current partial destination word, whether or not the input crosses. *)
Theorem eval_copyBits_partial_word_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < n <= cursor mod 64 ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  (64 - rc mod 64 < n -> bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (2 + rc / 64)) ->
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
  intros HS HF Hwrite Hlen Hn Hsep Hsepnext Hinput.
  destruct (Z_le_dec n (64 - rc mod 64)) as [Hshort|Hcross].
  - eapply eval_copyBits_short_layout; try eassumption; lia.
  - eapply eval_copyBits_partial_cross_layout; try eassumption; [lia|apply Hsepnext; lia].
Qed.
