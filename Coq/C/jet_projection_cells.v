(** Canonical projection encodings and initial input-buffer slicing.
    These discharge representation obligations of leftmost/rightmost jets;
    they do not execute the jets or discharge the external memcpy paths. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_context_separated C.jet_bitmachine_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma projection_vector_size (X : Ty) n :
  (bitSize X <= bitSize (Vector X n))%nat.
Proof. induction n; cbn [Vector bitSize]; lia. Qed.

Lemma encode_leftmost (X : Ty) n (v : Ty.tySem (Vector X n)) :
  encode (@leftmost X n Alg.CoreFunSem v) = firstn (bitSize X) (encode v).
Proof.
  induction n as [|n IH].
  - change (encode v = firstn (bitSize (Vector X 0)) (encode v)).
    rewrite <- (encode_length v). symmetry; apply firstn_all.
  - destruct v as [hi lo].
    change (encode (@leftmost X n Alg.CoreFunSem hi) =
      firstn (bitSize X) (encode hi ++ encode lo)).
    rewrite IH, firstn_app.
    assert (Hsize : (bitSize X - length (encode hi))%nat = 0%nat).
    { rewrite encode_length. apply Nat.sub_0_le. apply projection_vector_size. }
    rewrite Hsize. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma encode_rightmost (X : Ty) n (v : Ty.tySem (Vector X n)) :
  encode (@rightmost X n Alg.CoreFunSem v) =
    skipn (bitSize (Vector X n) - bitSize X) (encode v).
Proof.
  induction n as [|n IH].
  - change (encode v = skipn (bitSize X - bitSize X) (encode v)).
    rewrite Nat.sub_diag. reflexivity.
  - destruct v as [hi lo].
    change (encode (@rightmost X n Alg.CoreFunSem lo) =
      skipn (bitSize (Vector X n) + bitSize (Vector X n) - bitSize X)
        (encode hi ++ encode lo)).
    pose proof (projection_vector_size X n) as Hsize.
    rewrite IH, skipn_app.
    rewrite (skipn_all2 (n := bitSize (Vector X n) + bitSize (Vector X n) - bitSize X)
      (encode hi)) by (rewrite encode_length; lia).
    cbn [app]. rewrite encode_length.
    f_equal; lia.
Qed.

Lemma projection_input_firstn m bi edge rc cells n :
  frame_input_cells_at m bi edge rc cells ->
  frame_input_cells_at m bi edge rc (firstn n cells).
Proof.
  intros Hinput. rewrite <- (firstn_skipn n cells) in Hinput.
  apply frame_input_cells_at_app in Hinput. exact (proj1 Hinput).
Qed.

Lemma projection_input_skipn m bi edge rc cells n :
  (n <= length cells)%nat -> frame_input_cells_at m bi edge rc cells ->
  frame_input_cells_at m bi edge (rc + Z.of_nat n) (skipn n cells).
Proof.
  intros Hn Hinput. rewrite <- (firstn_skipn n cells) in Hinput.
  apply frame_input_cells_at_app in Hinput. destruct Hinput as [_ Hsuffix].
  rewrite firstn_length, Nat.min_l in Hsuffix by exact Hn. exact Hsuffix.
Qed.

Lemma projection_left_input m bi edge rc X n (v : Ty.tySem (Vector X n)) :
  frame_input_cells_at m bi edge rc (encode v) ->
  frame_input_cells_at m bi edge rc (encode (@leftmost X n Alg.CoreFunSem v)).
Proof. rewrite encode_leftmost. apply projection_input_firstn. Qed.

Lemma projection_right_input m bi edge rc X n (v : Ty.tySem (Vector X n)) :
  frame_input_cells_at m bi edge rc (encode v) ->
  frame_input_cells_at m bi edge
    (rc + Z.of_nat (bitSize (Vector X n) - bitSize X))
    (encode (@rightmost X n Alg.CoreFunSem v)).
Proof.
  rewrite encode_rightmost. intros Hinput. apply projection_input_skipn; [|exact Hinput].
  rewrite encode_length. lia.
Qed.

Lemma projection_buffers_slice bd bi bw edge outedge cursor rc total skip count :
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc total ->
  0 <= skip -> 0 <= count -> skip + count <= total ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor (rc + skip) count.
Proof.
  intros [HD [HB|HR]] Hskip Hcount Htotal; split; [exact HD|left; exact HB|exact HD|].
  right. unfold disjoint_ranges in *.
  pose proof (copy_frame_words_mono (rc + skip + count) (rc + total) ltac:(lia)) as Hwords.
  lia.
Qed.
