(** Connect the checked short-copy stores to the existing, algorithm-independent
    frame-cell observations, including undefined cells and written prefixes.
    The no-crossing restriction is explicit; these are not public jet proofs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
From compcert Require Import Clight ClightBigstep Events.
Require Import C.jets C.jet_exec C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_write_layout.
Require Import C.jet_copyBits_short_word C.jet_copyBits_short_exec.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_short_read_position rc j :
  0 <= j < 64 - rc mod 64 ->
  (rc + j) / 64 = rc / 64 /\ (rc + j) mod 64 = rc mod 64 + j.
Proof.
  intros Hj. pose proof (Z.mod_pos_bound rc 64 ltac:(lia)).
  pose proof (Z.div_mod rc 64 ltac:(lia)). apply div_mod_64; lia.
Qed.

Lemma copy_short_write_position cursor j :
  0 < cursor mod 64 -> 0 <= j < cursor mod 64 ->
  (cursor - 1 - j) / 64 = (cursor - 1) / 64 /\
  (cursor - 1 - j) mod 64 = cursor mod 64 - 1 - j.
Proof.
  intros Hpartial Hj. pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)).
  pose proof (Z.div_mod cursor 64 ltac:(lia)).
  destruct (div_mod_64 (cursor - 1) (cursor / 64) (cursor mod 64 - 1))
    as [Hq0 Hm0]; [lia|lia|].
  destruct (div_mod_64 (cursor - 1 - j) (cursor / 64) (cursor mod 64 - 1 - j))
    as [Hq Hm]; [lia|lia|]. split; congruence.
Qed.

Lemma copy_short_write_shift cursor :
  0 < cursor mod 64 -> write_word_shift cursor = cursor mod 64.
Proof.
  intros Hpartial.
  destruct (copy_short_write_position cursor 0 Hpartial ltac:(lia)) as [_ Hmod].
  rewrite Z.sub_0_r in Hmod. unfold write_word_shift; lia.
Qed.

Lemma copy_short_output_bit m mf bi edge rc bw outedge cursor n old source j bit :
  0 < cursor mod 64 -> 0 < n <= 64 - rc mod 64 -> n <= cursor mod 64 -> n <= cursor ->
  0 <= j < n ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  frame_input_bit_at m bi edge (rc + j) bit ->
  frame_output_bit_at mf bw outedge (cursor - 1 - j) bit.
Proof.
  intros Hpartial Hn Hnd HC Hj Hsource Hresult [_ [_ [w [HW Hb]]]].
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  destruct (copy_short_read_position rc j ltac:(lia)) as [Hqr Hmr].
  destruct (copy_short_write_position cursor j Hpartial ltac:(lia)) as [Hqw Hmw].
  rewrite Hqr in HW. rewrite Hsource in HW. injection HW as <-.
  split; [lia|]. exists (copy_short_value (64 - rc mod 64) (cursor mod 64) old source).
  rewrite Hqw, Hmw. split; [exact Hresult|].
  rewrite copy_short_copied_bit with (n := n) by lia.
  rewrite Hmr in Hb. replace (63 - (rc mod 64 + j)) with (64 - rc mod 64 - 1 - j) in Hb by lia.
  exact Hb.
Qed.

Lemma copy_short_output_cells m mf bi edge rc bw outedge cursor n old source cells :
  0 < cursor mod 64 -> 0 < n <= 64 - rc mod 64 -> n <= cursor mod 64 -> n <= cursor ->
  n = Z.of_nat (length cells) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 mf bw (write_word_address outedge cursor) =
    Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  frame_input_cells_at m bi edge rc cells ->
  frame_output_cells_at mf bw outedge cursor cells.
Proof.
  intros Hpartial Hn Hnd HC Hlen Hsource Hresult Hinput i cell Hnth.
  assert (Hi : 0 <= Z.of_nat i < n).
  { assert ((i < length cells)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  specialize (Hinput i cell Hnth). destruct cell as [bit|]; cbn [cell_matches] in *.
  - eapply copy_short_output_bit; eassumption.
  - destruct Hinput as [bit Hbit]. exists bit. eapply copy_short_output_bit; eassumption.
Qed.

Lemma copy_short_written_prefix m mf bw edge cursor rc old source :
  0 < cursor mod 64 ->
  Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old) ->
  Mem.load Mint64 mf bw (write_word_address edge cursor) =
    Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source)) ->
  write_prefix_at m mf bw edge cursor.
Proof.
  intros Hpartial Hold Hresult old' Hold'. rewrite Hold in Hold'. injection Hold' as <-.
  exists (copy_short_value (64 - rc mod 64) (cursor mod 64) old source).
  split; [exact Hresult|]. intros i Hi [Hlow|Hhigh]; [lia|].
  rewrite copy_short_write_shift in Hhigh by exact Hpartial.
  apply copy_short_existing_bit; pose proof (Z.mod_pos_bound rc 64 ltac:(lia));
    pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia.
Qed.

Lemma copy_input_cells_head m bi edge rc cells :
  0 < Z.of_nat (length cells) -> frame_input_cells_at m bi edge rc cells ->
  0 <= rc <= Int64.max_unsigned /\
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned /\
  exists source, Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source).
Proof.
  intros Hlen Hinput. destruct cells as [|cell cells]; [cbn in Hlen; lia|].
  specialize (Hinput 0%nat cell eq_refl).
  replace (rc + Z.of_nat 0) with rc in Hinput by lia.
  assert (Hbit : exists bit, frame_input_bit_at m bi edge rc bit).
  { destruct cell as [bit|]; cbn [cell_matches] in Hinput.
    - exists bit; exact Hinput.
    - exact Hinput. }
  destruct Hbit as [bit [HR [HE [source [HL Hb]]]]].
  repeat split; try lia. exists source; exact HL.
Qed.

Theorem eval_copyBits_short_layout m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n ->
  n = Z.of_nat (length cells) ->
  0 < n <= 64 - rc mod 64 -> n <= cursor mod 64 ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  frame_input_cells_at m bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m (Ctypes.Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (write_word_address outedge cursor) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HF Hwrite Hlen Hn Hnd Hsep Hinput.
  destruct (write_frame_at_head m bd base bw outedge cursor n ltac:(lia) Hwrite)
    as [HA0 [HAmax [PW [old Hold]]]].
  destruct Hwrite as [HB [HW [HO [HNcursor [HC [Hbd [PC Hwords]]]]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput)
    as [HR [HE [source Hsource]]].
  destruct (eval_copyBits_short m bd base bs sbase bi edge rc bw outedge cursor n old source
    HS HB HF HW HR ltac:(lia) HE HO ltac:(lia) ltac:(lia) Hn Hnd Hbd Hsep Hsource Hold PW PC)
    as [mf [Hcall [Hresult Hpost]]].
  exists mf. split; [exact Hcall|]. split.
  - eapply copy_short_output_cells; try eassumption; lia.
  - split; [eapply copy_short_written_prefix; try eassumption; lia|exact Hpost].
Qed.
