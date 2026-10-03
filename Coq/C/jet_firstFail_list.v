(** First-failure search bridge for length-bounded indexed list primitives.
    Used to connect literal count specifications to their C getter results. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_firstFail_spec C.jet_forWhile_search C.jet_word_repr.
Local Open Scope Z_scope.
Set Implicit Arguments.
Set Default Timeout 10.

Definition indexed_list_primitive n {X : Type} {B : Ty}
    (xs : list X) (encode : X -> tySem B) (w : tySem (Word n)) :
    option (tySem (Ty.Sum Ty.Unit B)) :=
  Some (match option_map encode (nth_error xs (Z.to_nat (@toZ (WordToZ n) w))) with
    | Some b => inr b | None => inl tt end).

Lemma first_fail_list_count n {X : Type} {B : Ty} (xs : list X) (encode : X -> tySem B) :
  Z.of_nat (length xs) < 2 ^ Z.of_nat (Nat.pow 2 n) ->
  first_fail_run n (indexed_list_primitive n xs encode) =
    Some (@fromZ (WordToZ n) (Z.of_nat (length xs))).
Proof.
  intro HBound.
  assert (HTarget : @toZ (WordToZ n) (@fromZ (WordToZ n) (Z.of_nat (length xs))) =
    Z.of_nat (length xs)).
  { rewrite to_fromZ, two_power_nat_equiv, word_bitSize.
    apply Z.mod_small. lia. }
  apply first_fail_run_first_left.
  - intros w Hw. rewrite HTarget in Hw.
    assert (HIndex : (Z.to_nat (@toZ (WordToZ n) w) < length xs)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by (pose proof (word_toZ_range n w); lia).
      exact Hw. }
    unfold indexed_list_primitive.
    destruct (nth_error xs (Z.to_nat (@toZ (WordToZ n) w))) as [x | ] eqn:HN.
    + exists (encode x). reflexivity.
    + apply nth_error_None in HN. lia.
  - exists tt. unfold indexed_list_primitive. rewrite HTarget, Nat2Z.id.
    assert (HN : nth_error xs (length xs) = None) by (apply nth_error_None; lia).
    rewrite HN. reflexivity.
Qed.
