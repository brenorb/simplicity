(** The two reader slices are consequences of the literal pair input encoding. *)
From Coq Require Import ZArith List.
From compcert Require Import Memory Values.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_encoding C.jet_input_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma field_pair_input_slices m bi edge rc (a b : Ty.tySem (Word 8)) :
  frame_input_cells_at m bi edge rc
    (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) ->
  frame_input_cells_at m bi edge rc (map Some (frame_input_word_bits a)) /\
  frame_input_cells_at m bi edge (rc+256) (map Some (frame_input_word_bits b)).
Proof.
  change (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) with (encode a ++ encode b).
  rewrite !encode_word.
  intro H. apply frame_input_cells_at_app in H.
  rewrite map_length, frame_input_word_bits_length in H.
  exact H.
Qed.
Print Assumptions field_pair_input_slices.
