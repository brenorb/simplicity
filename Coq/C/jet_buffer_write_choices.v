(** Derive actual buffer-writer tag decisions from canonical chunk sizes and
    the remaining present-byte length. Not individual jet coverage. *)
From Coq Require Import List Lia ZArith.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_read_buffer8_tag_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint byte_chunks_ordered (chunks : list byte_chunk) : Prop := match chunks with
  | [] => True
  | c :: cs => (byte_chunks_capacity cs < fst c)%nat /\ byte_chunks_ordered cs
  end.

Lemma buffer_byte_counts_capacity depth :
  S (fold_right Nat.add 0%nat (buffer_byte_counts depth)) = Nat.pow 2 (S depth).
Proof.
  induction depth as [|depth IH]; [reflexivity|].
  change (S (Nat.pow 2 (S depth) + fold_right Nat.add 0%nat (buffer_byte_counts depth)) =
    Nat.pow 2 (S (S depth))).
  cbn [Nat.pow] in IH |- *; lia.
Qed.

Lemma buffer_byte_chunks_ordered depth (x : Ty.tySem (buffer_type (Word 3) depth)) :
  byte_chunks_ordered (buffer_byte_chunks depth x).
Proof.
  induction depth as [|depth IH].
  - destruct x as [[]|x]; cbn [buffer_byte_chunks byte_chunks_ordered byte_chunks_capacity fst]; auto.
  - destruct x as [head tail].
    change ((byte_chunks_capacity (buffer_byte_chunks depth tail) < Nat.pow 2 (S depth))%nat /\
      byte_chunks_ordered (buffer_byte_chunks depth tail)). split; [|exact (IH tail)].
    rewrite byte_chunks_capacity_counts, buffer_byte_chunks_counts.
    pose proof (buffer_byte_counts_capacity depth); lia.
Qed.

Lemma byte_chunk_remaining_choice c cs :
  (match snd c with None => True | Some xs => length xs = fst c end) ->
  byte_chunks_sized cs -> (byte_chunks_capacity cs < fst c)%nat ->
  byte_chunk_tag c = (Z.of_nat (fst c) <=? Z.of_nat (length (byte_chunks_values (c :: cs)))).
Proof.
  intros HSize HSized HSmall. pose proof (byte_chunks_values_bound cs HSized) as HBound.
  destruct c as [n [xs|]]; cbn [snd fst byte_chunk_tag byte_chunks_values byte_chunk_values] in *.
  - rewrite app_length. symmetry; apply Z.leb_le; lia.
  - cbn [app length]. symmetry; apply Z.leb_gt; lia.
Qed.
