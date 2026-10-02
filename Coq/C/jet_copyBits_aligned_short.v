(** The actual aligned-destination, partial-source short-copy call, observed
    through logical frame cells. The first loop iteration returns before any
    memcpy or next-word load. No public jet coverage is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_copyBits_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_short_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_loop_value_bits ss source i :
  1 <= ss <= 63 -> 0 <= i < 64 ->
  Int64.testbit (copy_loop_value ss source) i =
    if zlt i (64 - ss) then false else Int64.testbit source (i - (64 - ss)).
Proof.
  intros Hss Hi. unfold copy_loop_value.
  rewrite Int64.bits_shl by exact Hi.
  rewrite Int64.unsigned_repr by (change (0 <= 64 - ss <= 18446744073709551615); lia).
  destruct (zlt i (64 - ss)); [reflexivity|].
  rewrite Int64.bits_zero_ext by lia. rewrite zlt_true by lia; reflexivity.
Qed.

Lemma copy_loop_copied_bit ss n source j :
  1 <= ss <= 63 -> 0 < n <= ss -> 0 <= j < n ->
  Int64.testbit (copy_loop_value ss source) (63 - j) = Int64.testbit source (ss - 1 - j).
Proof.
  intros Hss Hn Hj. rewrite copy_loop_value_bits by lia.
  rewrite zlt_false by lia. f_equal; lia.
Qed.

Lemma copy_aligned_write_position cursor j :
  cursor mod 64 = 0 -> 0 <= j < 64 ->
  (cursor - 1 - j) / 64 = (cursor - 1) / 64 /\ (cursor - 1 - j) mod 64 = 63 - j.
Proof.
  intros Hz Hj. pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64 - 1) 63) as [Hq0 Hm0]; [lia|lia|].
  destruct (div_mod_64 (cursor - 1 - j) (cursor / 64 - 1) (63 - j)) as [Hq Hm]; [lia|lia|].
  split; congruence.
Qed.

Lemma copy_aligned_write_shift cursor :
  cursor mod 64 = 0 -> write_word_shift cursor = 64.
Proof.
  intros Hz. destruct (copy_aligned_write_position cursor 0 Hz ltac:(lia)) as [_ Hm].
  rewrite Z.sub_0_r in Hm. unfold write_word_shift; lia.
Qed.

Lemma copy_aligned_short_output_bit m mf bi edge rc bw outedge cursor n source j bit :
  0 < rc mod 64 -> cursor mod 64 = 0 ->
  0 < n <= 64 - rc mod 64 -> n <= cursor -> 0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_loop_value (64 - rc mod 64) source)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hsrc Hz Hn HC Hj Hsource Hresult [_ [_ [w [HW Hb]]]].
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  destruct (copy_short_read_position rc j ltac:(lia)) as [Hqr Hmr].
  destruct (copy_aligned_write_position cursor j Hz ltac:(lia)) as [Hqw Hmw].
  rewrite Hqr in HW. rewrite Hsource in HW. injection HW as <-.
  split; [lia|]. exists (copy_loop_value (64 - rc mod 64) source).
  rewrite Hqw, Hmw. split; [exact Hresult|].
  rewrite copy_loop_copied_bit with (n := n) by lia.
  rewrite Hmr in Hb. replace (63 - (rc mod 64 + j)) with (64 - rc mod 64 - 1 - j) in Hb by lia.
  exact Hb.
Qed.

Lemma copy_aligned_short_output_cells m mf bi edge rc bw outedge cursor n source cells :
  0 < rc mod 64 -> cursor mod 64 = 0 ->
  0 < n <= 64 - rc mod 64 -> n <= cursor -> n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_loop_value (64 - rc mod 64) source)) ->
  frame_input_cells_at m bi edge rc cells ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hsrc Hz Hn HC Hlen Hsource Hresult Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_aligned_short_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_aligned_short_output_bit; eassumption.
Qed.

Lemma copy_aligned_written_prefix m mf bw edge cursor value :
  cursor mod 64 = 0 -> Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong value) ->
  write_prefix_at m mf bw edge cursor.
Proof.
  intros Hz Hresult old Hold. exists value. split; [exact Hresult|].
  intros i Hi Houtside. rewrite copy_aligned_write_shift in Houtside by exact Hz. lia.
Qed.

Theorem eval_copyBits_aligned_short_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < rc mod 64 -> cursor mod 64 = 0 -> 0 < n <= 64 - rc mod 64 ->
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
  intros HS HF Hwrite Hlen Hsrc Hz Hn Hinput.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (eval_copy_helper_aligned_short m bd base bs sbase bi edge rc bw outedge cursor n source
    HS HB HF HW HR ltac:(lia) HE HO ltac:(lia) Hsrc Hz Hn ltac:(lia) Hbd Hsource PW)
    as [mi [Hcall [Hword [Hfields [Houtside [Hperm Hvalid]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HC Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hresult : Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_loop_value (64 - rc mod 64) source))).
  { rewrite HcursorOutside; [exact Hword|left; congruence]. }
  exists mf. split; [exact Hwrapper|]. split.
  - eapply copy_aligned_short_output_cells; try eassumption; lia.
  - split; [eapply copy_aligned_written_prefix; eassumption|].
    split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor. apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
