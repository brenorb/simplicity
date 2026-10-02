(** Canonical word encoding as a sequence of uint32-sized chunks.
    These representation lemmas support array-based jets; they are not
    implementation-to-specification proofs for those jets. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_input_layout C.jet_encoding C.jet_read32s_layout C.jet_toZ C.jet_read32_input_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint word32_chunks n : Ty.tySem (Word (n + 5)) -> list (Ty.tySem (Word 5)) :=
  match n as k return Ty.tySem (Word (k + 5)) -> list (Ty.tySem (Word 5)) with
  | O => fun x => [x]
  | S k => fun x => word32_chunks k (fst x) ++ word32_chunks k (snd x)
  end.
Lemma word32_chunks_length n x : length (word32_chunks n x) = Nat.pow 2 n.
Proof.
  revert x. induction n; intros x; [reflexivity|].
  cbn [word32_chunks]. rewrite app_length, !IHn. cbn [Nat.pow]. lia.
Qed.
Lemma word32_chunks_encode n x :
  @encode (Word (n + 5)) x = concat (map (@encode (Word 5)) (word32_chunks n x)).
Proof.
  revert x. induction n; intros x.
  - cbn [word32_chunks map concat]. rewrite app_nil_r; reflexivity.
  - destruct x as [hi lo].
    change (encode hi ++ encode lo =
      concat (map (@encode (Word 5)) (word32_chunks n hi ++ word32_chunks n lo))).
    rewrite map_app, concat_app, <- !IHn. reflexivity.
Qed.
Lemma word32_chunks_injective n (x y : Ty.tySem (Word (n + 5))) :
  word32_chunks n x = word32_chunks n y -> x = y.
Proof.
  revert x y. induction n; intros x y H.
  - cbn [word32_chunks] in H. injection H; auto.
  - destruct x as [xh xl], y as [yh yl]. cbn [word32_chunks] in H.
    destruct (app_eq_app _ _ _ _ H) as [rest [[HL HR]|[HL HR]]].
    all: assert (HZ : rest = []) by
      (pose proof (f_equal (@length (Ty.tySem (Word 5))) HL) as Hlen;
      rewrite app_length, !word32_chunks_length in Hlen;
      apply length_zero_iff_nil; lia).
    all: subst rest; rewrite app_nil_r in HL; cbn [app] in HR;
      cbn [fst snd] in HL, HR;
      f_equal; apply IHn; congruence.
Qed.

Lemma frame_input_word32_sequence m bi edge cursor xs :
  frame_input_cells_at m bi edge cursor (concat (map (@encode (Word 5)) xs)) ->
  forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 32 * Z.of_nat i) x.
Proof.
  revert cursor. induction xs as [|head xs IH]; intros cursor HI [|i] x Hx; try discriminate.
  - cbn [map concat] in HI. apply frame_input_cells_at_app in HI.
    cbn in Hx. injection Hx as <-.
    replace (cursor + 32 * Z.of_nat O) with cursor by lia.
    apply frame_input_word_at_encode. exact (proj1 HI).
  - cbn [map concat] in HI. apply frame_input_cells_at_app in HI.
    destruct HI as [_ HI]. rewrite (encode_word_length 5 head) in HI.
    change (frame_input_cells_at m bi edge (cursor + 32)
      (concat (map (@encode (Word 5)) xs))) in HI.
    replace (cursor + 32 * Z.of_nat (S i)) with (cursor + 32 + 32 * Z.of_nat i) by lia.
    exact (IH (cursor + 32) HI i x Hx).
Qed.
Lemma frame_input_word32_chunks m bi edge cursor n x :
  frame_input_cells_at m bi edge cursor (@encode (Word (n + 5)) x) ->
  forall i y, nth_error (word32_chunks n x) i = Some y ->
    frame_input_word_at m bi edge (cursor + 32 * Z.of_nat i) y.
Proof. rewrite word32_chunks_encode. apply frame_input_word32_sequence. Qed.

Lemma word32_array_value_injective (x y : Ty.tySem (Word 5)) :
  word32_array_value x = word32_array_value y -> x = y.
Proof.
  intros H. apply (toZ_injective (WordToZ 5)).
  apply (f_equal Int.unsigned) in H. unfold word32_array_value in H.
  rewrite !Int.unsigned_repr in H by
    (change Int.max_unsigned with 4294967295;
      first [pose proof (word32_toZ_range x); lia|pose proof (word32_toZ_range y); lia]).
  exact H.
Qed.
