(** Word-slice representations agree with the Simplicity word decoder. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word C.jet_spec C.jet_word_bits C.jet_frame_spec.
Local Open Scope Z_scope.

Lemma decode_word8_projection w : decode_word8 (Int64.zero_ext 8 w) = decode_word8 w.
Proof.
  unfold decode_word8.
  rewrite Int64.zero_ext_mod by (change (0 <= 8 < 64); lia).
  pose proof (@from_toZ (WordToZ 3) (@fromZ (WordToZ 3) (Int64.unsigned w))) as H.
  rewrite to_fromZ in H. exact H.
Qed.

Lemma decode_word8_put old payload :
  decode_word8 (put_low 8 old payload) = decode_word8 payload.
Proof.
  rewrite <- (decode_word8_projection (put_low 8 old payload)).
  rewrite put_low_projection by lia. apply decode_word8_projection.
Qed.

Lemma put_low_outside n old payload :
  1 <= n <= 64 -> word_outside_eq 0 n (put_low n old payload) old.
Proof.
  intros Hn i Hi Houtside.
  rewrite put_low_bits by assumption. rewrite zlt_false by lia. reflexivity.
Qed.

Lemma put_low_slice n old payload :
  1 <= n <= 64 -> word_slice_eq 0 n (put_low n old payload) payload.
Proof.
  intros Hn i Hi. rewrite put_low_bits by lia.
  rewrite zlt_true by lia. reflexivity.
Qed.
