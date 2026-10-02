(** Derive the word-level protections needed by actual copy stores from the
    represented caller's existing whole-buffer separation. No stronger caller
    layout restriction is introduced; these lemmas add no public jet coverage. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers Values.
Require Import C.jet_write_layout C.jet_bitmachine_rep C.jet_context_separated.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_read_word_region edge rc count j :
  0 <= rc -> 0 <= j < count ->
  edge - 8 * frame_words (rc + count) <= edge - 8 * (1 + (rc + j) / 64) /\
  edge - 8 * (1 + (rc + j) / 64) + 8 <= edge.
Proof.
  intros HR Hj. pose proof (frame_words_bounds (rc + count) ltac:(lia)) as HF.
  pose proof (Z.div_pos (rc + j) 64 ltac:(lia) ltac:(lia)) as HQ.
  pose proof (Z.div_mod (rc + j) 64 ltac:(lia)) as HE.
  pose proof (Z.mod_pos_bound (rc + j) 64 ltac:(lia)) as HM. lia.
Qed.

Lemma copy_write_word_region edge cursor j :
  0 <= j < cursor ->
  edge <= write_word_address edge (cursor - j) /\
  write_word_address edge (cursor - j) + 8 <= edge + 8 * frame_words cursor.
Proof.
  intros Hj. unfold write_word_address.
  pose proof (frame_words_bounds cursor ltac:(lia)) as HF.
  pose proof (Z.div_pos (cursor - j - 1) 64 ltac:(lia) ltac:(lia)) as HQ.
  pose proof (Z.div_mod (cursor - j - 1) 64 ltac:(lia)) as HE.
  pose proof (Z.mod_pos_bound (cursor - j - 1) 64 ltac:(lia)) as HM. lia.
Qed.

Lemma copy_buffers_separated_words bd bi bw edge outedge cursor rc count j k :
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc count ->
  0 <= rc -> 0 <= j < count -> 0 <= k < cursor ->
  bi <> bw \/
    edge - 8 * (1 + (rc + j) / 64) + 8 <= write_word_address outedge (cursor - k) \/
    write_word_address outedge (cursor - k) + 8 <= edge - 8 * (1 + (rc + j) / 64).
Proof.
  intros [_ [Hblocks|Hranges]] HR Hj Hk; [left; exact Hblocks|].
  destruct (copy_read_word_region edge rc count j HR Hj) as [Hrl Hrh].
  destruct (copy_write_word_region outedge cursor k Hk) as [Hwl Hwh].
  unfold disjoint_ranges in Hranges. right. lia.
Qed.
