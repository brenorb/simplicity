(** Unread input survives output effects under the actual Bit Machine ranges.
    Read and write data may share [cells_blk]; no distinct-data-block premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_elements_effects C.jet_elements_env_load C.jet_application_sep C.jet_bitmachine_rep.
Import Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma write_effect_input_bits_preserved m mf bd dbase bw edge cur count cells bi inedge rc bits :
  0 < count -> count <= cur -> write_effect m mf bd dbase bw edge cur count cells ->
  (forall k, 0 <= k < Z.of_nat (length bits) ->
    out_sep bd dbase bw edge cur count bi
      (inedge - 8 * (1 + (rc + k) / 64)) (inedge - 8 * (1 + (rc + k) / 64) + 8)) ->
  frame_input_bits_at m bi inedge rc bits -> frame_input_bits_at mf bi inedge rc bits.
Proof.
  intros Hn Hcur HE HS HI k bit Hnth.
  assert (HK : (k < length bits)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
  destruct (HI k bit Hnth) as (HQ & HEdge & w & HL & HB).
  unfold frame_input_bit_at. split; [exact HQ|]. split; [exact HEdge|]. exists w. split; [|exact HB].
  rewrite (write_effect_env_load m mf bd dbase bw edge cur count cells cur count bi
    (inedge - 8 * (1 + (rc + Z.of_nat k) / 64)) (inedge - 8 * (1 + (rc + Z.of_nat k) / 64) + 8)
    Mint64 (inedge - 8 * (1 + (rc + Z.of_nat k) / 64)))
    by (first [exact Hn | exact Hcur | exact HE | apply HS; lia | change (size_chunk Mint64) with 8; lia | lia]).
  exact HL.
Qed.

Lemma read_frame_word_bounds l rf q :
  0 <= q < read_size rf ->
  read_region_lo l rf <= edge_ofs l - 8 * (1 + (read_padding (read_size rf) + q) / 64) /\
  edge_ofs l - 8 * (1 + (read_padding (read_size rf) + q) / 64) + 8 <= edge_ofs l.
Proof.
  intros HQ. pose proof (frame_words_bounds (read_size rf) ltac:(lia)) as [HW HBounds].
  unfold read_region_lo, read_padding.
  assert (Hdiv : 0 <= (64 * frame_words (read_size rf) - read_size rf + q) / 64 < frame_words (read_size rf)).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  split; lia.
Qed.

Lemma write_effect_region_bounds l wf count :
  0 < count <= Z.of_nat (writeEmpty wf) ->
  edge_ofs l <= out_low (edge_ofs l) (Z.of_nat (writeEmpty wf)) count /\
  out_high (edge_ofs l) (Z.of_nat (writeEmpty wf)) <= write_region_hi l wf.
Proof.
  intros Hcount.
  assert (HW0 : 0 <= write_size wf) by (unfold write_size; lia).
  pose proof (frame_words_bounds (write_size wf) HW0) as [HW HBounds].
  assert (Hcur : Z.of_nat (writeEmpty wf) <= write_size wf) by
    (unfold write_size; rewrite Nat2Z.inj_add; lia).
  unfold out_low, out_high, write_word_address, write_region_hi.
  assert (Hlo : 0 <= (Z.of_nat (writeEmpty wf) - count) / 64) by (apply Z.div_pos; lia).
  assert (Hhi : (Z.of_nat (writeEmpty wf) - 1) / 64 < frame_words (write_size wf)) by
    (apply Z.div_lt_upper_bound; lia).
  split; lia.
Qed.

Lemma bm_active_read_word_out_sep m L s count q :
  bm_rep m L s -> bm_separated L s -> 0 < count <= Z.of_nat (writeEmpty (activeWriteFrame s)) ->
  0 <= q < read_size (activeReadFrame s) ->
  out_sep (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L) (edge_ofs (active_write_loc L))
    (Z.of_nat (writeEmpty (activeWriteFrame s))) count (cells_blk L)
    (edge_ofs (active_read_loc L) - 8 * (1 + (read_padding (read_size (activeReadFrame s)) + q) / 64))
    (edge_ofs (active_read_loc L) - 8 * (1 + (read_padding (read_size (activeReadFrame s)) + q) / 64) + 8).
Proof.
  intros [Hblocks _] HSep Hcount HQ.
  unfold bm_separated in HSep. destruct HSep as (Hitems & Hreads & Hwrites).
  inversion Hreads as [|l rf ls rfs HD HR]; subst.
  pose proof (read_frame_word_bounds (active_read_loc L) (activeReadFrame s) q HQ) as [Hrl Hrh].
  pose proof (write_effect_region_bounds (active_write_loc L) (activeWriteFrame s) count Hcount) as [Hwl Hwh].
  split; [left; exact Hblocks|]. unfold disjoint_ranges in HD.
  destruct HD as [HD|HD]; [right; right|right; left]; lia.
Qed.

Theorem write_effect_keeps_active_read_suffix m mf L s count cells start bits :
  bm_rep m L s -> bm_separated L s -> 0 < count <= Z.of_nat (writeEmpty (activeWriteFrame s)) ->
  0 <= start -> start + Z.of_nat (length bits) <= read_size (activeReadFrame s) ->
  write_effect m mf (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L)
    (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s))) count cells ->
  frame_input_bits_at m (cells_blk L) (edge_ofs (active_read_loc L))
    (read_padding (read_size (activeReadFrame s)) + start) bits ->
  frame_input_bits_at mf (cells_blk L) (edge_ofs (active_read_loc L))
    (read_padding (read_size (activeReadFrame s)) + start) bits.
Proof.
  intros HBM HSep Hcount Hstart Hsize HE HI.
  eapply write_effect_input_bits_preserved with (count := count)
    (cur := Z.of_nat (writeEmpty (activeWriteFrame s))); [lia|lia|exact HE| |exact HI].
  intros k HK.
  replace (read_padding (read_size (activeReadFrame s)) + start + k) with
    (read_padding (read_size (activeReadFrame s)) + (start + k)) by lia.
  eapply bm_active_read_word_out_sep; [exact HBM|exact HSep|exact Hcount|lia].
Qed.

Lemma write_effect_keeps_private_read_frame m mf bd dbase bw edge cur count cells bl base bi inedge rc :
  bl <> bd -> bl <> bw -> write_effect m mf bd dbase bw edge cur count cells ->
  frame_fields_at m bl base bi inedge rc -> frame_fields_at mf bl base bi inedge rc.
Proof.
  intros HD HW (_ & _ & _ & HLoads & _) [Hedge Hrc]. split.
  - rewrite HLoads by (left; assumption). exact Hedge.
  - rewrite HLoads by (left; assumption). exact Hrc.
Qed.

Lemma write_effect_keeps_valid_access m mf bd dbase bw edge cur count cells chunk b ofs p :
  write_effect m mf bd dbase bw edge cur count cells ->
  Mem.valid_access m chunk b ofs p -> Mem.valid_access mf chunk b ofs p.
Proof.
  intros (_ & _ & _ & _ & HPerm & _) [HR HA]. split; [|exact HA].
  intros k HK. apply HPerm, HR; exact HK.
Qed.
