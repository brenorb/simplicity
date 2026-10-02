(** Logical cell observations of the actual two-store, first-iteration return.
    Input-word crossings are supported; the destination is one aligned word.
    This helper contract adds no public jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_copyBits_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing C.jet_copyBits_aligned_short.
Require Import C.jet_copyBits_short_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_loop_join_value_bits ss source next i :
  1 <= ss <= 63 -> 0 <= i < 64 ->
  Int64.testbit (copy_loop_join_value ss source next) i =
    if zlt i (64 - ss) then Int64.testbit next (i + ss)
    else Int64.testbit source (i - (64 - ss)).
Proof.
  intros Hss Hi. unfold copy_loop_join_value.
  rewrite Int64.bits_or by exact Hi.
  rewrite copy_loop_value_bits by assumption.
  rewrite Int64.bits_shru by exact Hi.
  rewrite Int64.unsigned_repr by (change (0 <= ss <= 18446744073709551615); lia).
  destruct (zlt i (64 - ss)).
  - rewrite zlt_true by (change (i + ss < 64); lia); reflexivity.
  - rewrite zlt_false by (change (~ i + ss < 64); lia); apply orb_false_r.
Qed.

Lemma copy_loop_join_copied_bit ss n source next j :
  1 <= ss <= 63 -> ss < n <= 64 -> 0 <= j < n ->
  Int64.testbit (copy_loop_join_value ss source next) (63 - j) =
    if zlt j ss then Int64.testbit source (ss - 1 - j)
    else Int64.testbit next (63 - (j - ss)).
Proof.
  intros Hss Hn Hj. rewrite copy_loop_join_value_bits by lia.
  destruct (zlt j ss).
  - rewrite zlt_false by lia. f_equal; lia.
  - rewrite zlt_true by lia. f_equal; lia.
Qed.

Lemma copy_crossing_read_position rc j :
  64 - rc mod 64 <= j < 128 - rc mod 64 ->
  (rc + j) / 64 = rc / 64 + 1 /\ (rc + j) mod 64 = j - (64 - rc mod 64).
Proof.
  intros Hj. pose proof (Z.mod_pos_bound rc 64 ltac:(lia)).
  pose proof (Z.div_mod rc 64 ltac:(lia)). apply div_mod_64; lia.
Qed.

Lemma copy_aligned_crossing_output_bit m mf bi edge rc bw outedge cursor n source next j bit :
  0 < rc mod 64 -> cursor mod 64 = 0 ->
  64 - rc mod 64 < n <= 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_loop_join_value (64 - rc mod 64) source next)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hsrc Hz Hn HC Hj Hsource Hnext Hresult [_ [_ [w [HW Hb]]]].
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  destruct (copy_aligned_write_position cursor j Hz ltac:(lia)) as [Hqw Hmw].
  split; [lia|]. exists (copy_loop_join_value (64 - rc mod 64) source next).
  rewrite Hqw, Hmw. split; [exact Hresult|].
  rewrite copy_loop_join_copied_bit with (n := n) by lia.
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

Lemma copy_aligned_crossing_output_cells m mf bi edge rc bw outedge cursor n source next cells :
  0 < rc mod 64 -> cursor mod 64 = 0 ->
  64 - rc mod 64 < n <= 64 -> n <= cursor -> n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_loop_join_value (64 - rc mod 64) source next)) ->
  frame_input_cells_at m bi edge rc cells ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hsrc Hz Hn HC Hlen Hsource Hnext Hresult Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_aligned_crossing_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_aligned_crossing_output_bit; eassumption.
Qed.

Lemma copy_crossing_input_word m bi edge rc n cells :
  0 < rc mod 64 -> 64 - rc mod 64 < n <= 64 -> n = Z.of_nat (length cells) ->
  frame_input_cells_at m bi edge rc cells ->
  8 * (2 + rc / 64) <= edge <= Ptrofs.max_unsigned /\
  exists next, Mem.load Mint64 m bi (edge - 8 * (2 + rc / 64)) = Some (Vlong next).
Proof.
  intros Hsrc Hn Hlen Hinput. pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  set (i := Z.to_nat (64 - rc mod 64)).
  assert (Hi : (i < length cells)%nat) by (unfold i; lia).
  destruct (nth_error cells i) as [cell|] eqn:Hnth; [|apply nth_error_None in Hnth; lia].
  specialize (Hinput i cell Hnth).
  replace (rc + Z.of_nat i) with (rc + (64 - rc mod 64)) in Hinput by (unfold i; lia).
  assert (Hbit : exists bit, frame_input_bit_at m bi edge (rc + (64 - rc mod 64)) bit).
  { destruct cell as [bit|]; cbn [cell_matches] in Hinput.
    - exists bit; exact Hinput.
    - exact Hinput. }
  destruct Hbit as [bit [_ [HE [next [HL Hb]]]]].
  destruct (copy_crossing_read_position rc (64 - rc mod 64) ltac:(lia)) as [Hq _].
  rewrite Hq in HE, HL.
  replace (1 + (rc / 64 + 1)) with (2 + rc / 64) in HE, HL by lia.
  split; [exact HE|]. exists next; exact HL.
Qed.

Theorem eval_copyBits_aligned_crossing_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < rc mod 64 -> cursor mod 64 = 0 -> 64 - rc mod 64 < n <= 64 ->
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
  intros HS HF Hwrite Hlen Hsrc Hz Hn Hsep Hinput.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (copy_crossing_input_word m bi edge rc n cells Hsrc Hn Hlen Hinput)
    as [HE2 [next Hnext]].
  destruct (eval_copy_helper_aligned_full m bd base bs sbase bi edge rc bw outedge cursor n source next
    HS HB HF HW HR ltac:(lia) HE2 HO ltac:(lia) Hsrc Hz Hn ltac:(lia) Hbd Hsep Hsource Hnext PW)
    as [mi [Hcall [Hword [Hfields [Houtside [Hperm Hvalid]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hresult : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_loop_join_value (64 - rc mod 64) source next))).
  { rewrite HcursorOutside; [exact Hword|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_aligned_crossing_output_cells; try eassumption; lia.
  - split; [eapply copy_aligned_written_prefix; eassumption|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.

(** Both return cases for every positive count up to 64, with a partial
    source and aligned destination. Separation is needed only when crossing. *)
Theorem eval_copyBits_aligned_partial_source_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < rc mod 64 -> cursor mod 64 = 0 -> 0 < n <= 64 ->
  (64 - rc mod 64 < n ->
    bi <> bw \/ edge - 8 * (2 + rc / 64) + 8 <= write_word_address outedge cursor \/
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
  intros HS HF Hwrite Hlen Hsrc Hz Hn Hsep Hinput.
  destruct (Z_le_dec n (64 - rc mod 64)) as [Hshort|Hcross].
  - eapply eval_copyBits_aligned_short_layout; eassumption || lia.
  - eapply eval_copyBits_aligned_crossing_layout; try eassumption; [lia|apply Hsep; lia].
Qed.
