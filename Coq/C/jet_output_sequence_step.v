(** Shared memory composition for successive word writes.  These contracts
    retain arbitrary initial contents and all valid cursor crossings. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_slice C.jet_encoding.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma write_frame_at_after_slice m mf bf base bw edge cursor n count x :
  0 <= count -> 1 <= n <= 64 ->
  write_frame_at m bf base bw edge cursor (n + count) ->
  frame_fields_at mf bf base bw edge (cursor - n) ->
  slice_output_at n mf bw edge cursor x ->
  loads_outside_ranges m mf bf (base + 8) (base + 16)
    bw (slice_write_low n edge cursor) (write_word_address edge cursor + 8) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  write_frame_at mf bf base bw edge (cursor - n) count.
Proof.
  intros Hcount Hn [HB [HF [HE [HC [HM [PD HW]]]]]] HF' HO HL HP.
  assert (HV : forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
    Mem.valid_access mf chunk b ofs p).
  { intros chunk b ofs p [HR HA]. split; [|exact HA]. intros addr HA'. apply HP, HR; exact HA'. }
  split; [exact HB|]. split; [exact HF'|]. split; [exact HE|]. split; [lia|].
  split; [lia|]. split; [auto|].
  intros i Hi. cbn zeta.
  assert (Haddr : write_cell_address edge (cursor - n) i = write_cell_address edge cursor (i + n)).
  { unfold write_cell_address. replace (cursor - n - 1 - i) with (cursor - 1 - (i + n)) by lia.
    reflexivity. }
  rewrite Haddr. destruct (HW (i + n) ltac:(lia)) as [HA0 [HA [HD [PW [old Hold]]]]].
  split; [exact HA0|]. split; [exact HA|]. split; [exact HD|]. split; [auto|].
  assert (Hcursorsep : bw <> bf \/
      write_cell_address edge cursor (i + n) + 8 <= base + 8 \/
      base + 16 <= write_cell_address edge cursor (i + n)).
  { destruct HD as [HD|[HD|HD]]; [left; congruence|right; left; lia|right; right; exact HD]. }
  unfold slice_output_at in HO. unfold slice_write_low in HL.
  destruct (Z_le_dec n (write_word_shift cursor)) as [Hfits|Hcross].
  - destruct HO as [w [Hword _]].
    destruct (Z.eq_dec (write_cell_address edge cursor (i + n)) (write_word_address edge cursor))
      as [Heq|Hneq].
    + rewrite Heq. exists w; exact Hword.
    + exists old. rewrite HL; [exact Hold|exact Hcursorsep|]. right.
      unfold write_cell_address, write_word_address in Hneq |- *.
      change (size_chunk Mint64) with 8. lia.
  - destruct HO as [high [low [Hhigh [Hlow _]]]].
    destruct (Z.eq_dec (write_cell_address edge cursor (i + n)) (write_word_address edge cursor))
      as [Heq|Hneq].
    + rewrite Heq. exists high; exact Hhigh.
    + destruct (Z.eq_dec (write_cell_address edge cursor (i + n)) (write_word_address edge cursor - 8))
        as [HeqLow|HneqLow].
      * rewrite HeqLow. exists low; exact Hlow.
      * exists old. rewrite HL; [exact Hold|exact Hcursorsep|]. right.
        unfold write_cell_address, write_word_address in Hneq, HneqLow |- *.
        change (size_chunk Mint64) with 8. lia.
Qed.

Lemma write_prefix_at_chain m mi mf bf base bw edge cursor next low :
  (bf <> bw \/ write_word_address edge cursor + 8 <= base \/
    base + 16 <= write_word_address edge cursor) -> 0 <= next <= cursor ->
  write_prefix_at m mi bw edge cursor -> write_prefix_at mi mf bw edge next ->
  loads_outside_ranges mi mf bf (base + 8) (base + 16)
    bw low (write_word_address edge next + 8) ->
  write_prefix_at m mf bw edge cursor.
Proof.
  intros HD HC Hfirst Hnext HL old Hold.
  destruct (Hfirst old Hold) as [middle [Hmiddle Hsame]].
  pose proof (Z.div_le_mono (next - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)) as Hq.
  destruct (Z.eq_dec (write_word_address edge next) (write_word_address edge cursor))
    as [Heq|Hneq].
  - assert (Hshift : write_word_shift next <= write_word_shift cursor).
    { unfold write_word_address in Heq. unfold write_word_shift.
      pose proof (Z.div_mod (next - 1) 64 ltac:(lia)).
      pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)). lia. }
    destruct (Hnext middle ltac:(rewrite Heq; exact Hmiddle)) as [w [Hword Hnew]].
    exists w. split; [rewrite <- Heq; exact Hword|].
    intros i Hi Hout. rewrite Hnew; [apply Hsame; assumption|exact Hi|lia].
  - exists middle. split; [|exact Hsame].
    rewrite HL; [exact Hmiddle|
      change (bw <> bf \/ write_word_address edge cursor + 8 <= base + 8 \/
        base + 16 <= write_word_address edge cursor);
      destruct HD as [HD|[HD|HD]]; [left; congruence|right; left; lia|right; right; exact HD]
    |right; right].
    unfold write_word_address in Hneq |- *. lia.
Qed.

Lemma frame_output_bit_prefix_preserved m mf bf base bw edge cursor low q bit :
  (bf <> bw \/ edge + 8 * (q / 64) + 8 <= base \/
    base + 16 <= edge + 8 * (q / 64)) -> 0 <= cursor <= q ->
  write_prefix_at m mf bw edge cursor ->
  loads_outside_ranges m mf bf (base + 8) (base + 16)
    bw low (write_word_address edge cursor + 8) ->
  frame_output_bit_at m bw edge q bit -> frame_output_bit_at mf bw edge q bit.
Proof.
  intros HD HC HP HL [HQ [old [Hold Hbit]]]. split; [exact HQ|].
  pose proof (Z.div_le_mono (cursor - 1) q 64 ltac:(lia) ltac:(lia)) as Hq.
  destruct (Z.eq_dec (edge + 8 * (q / 64)) (write_word_address edge cursor)) as [Heq|Hneq].
  - assert (Hpos : write_word_shift cursor <= q mod 64).
    { unfold write_word_address in Heq. unfold write_word_shift.
      pose proof (Z.div_mod q 64 ltac:(lia)).
      pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)). lia. }
    destruct (HP old ltac:(rewrite <- Heq; exact Hold)) as [w [Hword Hsame]].
    exists w. split; [rewrite Heq; exact Hword|].
    rewrite Hbit. symmetry. apply Hsame.
    + apply Z.mod_pos_bound; lia.
    + right; lia.
  - exists old. split; [|exact Hbit].
    rewrite HL; [exact Hold|
      change (bw <> bf \/ edge + 8 * (q / 64) + 8 <= base + 8 \/
        base + 16 <= edge + 8 * (q / 64));
      destruct HD as [HD|[HD|HD]]; [left; congruence|right; left; lia|right; right; exact HD]
    |right; right].
    unfold write_word_address in Hneq |- *. lia.
Qed.

Lemma frame_output_cells_prefix_preserved m mf bf base bw edge cursor low original cells :
  (forall i, (i < length cells)%nat ->
    bf <> bw \/ write_cell_address edge original (Z.of_nat i) + 8 <= base \/
      base + 16 <= write_cell_address edge original (Z.of_nat i)) -> 0 <= cursor <= original - Z.of_nat (length cells) ->
  write_prefix_at m mf bw edge cursor ->
  loads_outside_ranges m mf bf (base + 8) (base + 16)
    bw low (write_word_address edge cursor + 8) ->
  frame_output_cells_at m bw edge original cells -> frame_output_cells_at mf bw edge original cells.
Proof.
  intros HD HC HP HL HO i c Hi.
  assert (HI : (i < length cells)%nat).
  { apply nth_error_Some. rewrite Hi; discriminate. }
  specialize (HD i HI). unfold write_cell_address in HD.
  specialize (HO i c Hi). destruct c as [bit|]; cbn [cell_matches] in *.
  - eapply frame_output_bit_prefix_preserved; eauto; lia.
  - destruct HO as [bit HO]. exists bit. eapply frame_output_bit_prefix_preserved; eauto; lia.
Qed.
