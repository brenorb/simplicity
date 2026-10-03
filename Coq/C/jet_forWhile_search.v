(** Symbolic ordered-search invariants for the literal forWhile interpretation.
    No enumeration of wide words and no public C-jet coverage. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_forWhile_spec C.jet_firstFail_spec C.jet_word_repr.
Local Open Scope ty_scope.
Local Open Scope Z_scope.
Set Implicit Arguments.
Set Default Timeout 10.

Lemma for_while_run_all_right n {C B A : Ty}
    (body : tySem (Ty.Prod (Ty.Prod C (Word n)) A) -> option (tySem (Ty.Sum B A)))
    (context : tySem C) (state : tySem A) :
  (forall w, body ((context, w), state) = Some (inr state)) ->
  for_while_run n body context state = Some (inr state).
Proof.
  revert C B A body context state. induction n; intros C B A body context state HB.
  - cbn [for_while_run]. rewrite HB. apply HB.
  - cbn [for_while_run]. apply IHn. intro hi.
    apply IHn. intro lo. apply HB.
Qed.

Lemma search_word_pair_lt_high n (hi lo hi' lo' : tySem (Word n)) :
  @toZ (WordToZ n) hi < @toZ (WordToZ n) hi' ->
  @toZ (WordToZ (S n)) (hi, lo) < @toZ (WordToZ (S n)) (hi', lo').
Proof.
  intro Hhi.
  change (@toZ (WordToZ n) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo <
    @toZ (WordToZ n) hi' * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo').
  rewrite two_power_nat_equiv, word_bitSize.
  pose proof (word_toZ_range n lo). pose proof (word_toZ_range n lo'). nia.
Qed.

Lemma search_word_pair_lt_low n (hi lo lo' : tySem (Word n)) :
  @toZ (WordToZ n) lo < @toZ (WordToZ n) lo' ->
  @toZ (WordToZ (S n)) (hi, lo) < @toZ (WordToZ (S n)) (hi, lo').
Proof.
  intro Hlo.
  change (@toZ (WordToZ n) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo <
    @toZ (WordToZ n) hi * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) lo'). lia.
Qed.

Lemma for_while_run_first_left n {C B A : Ty}
    (body : tySem (Ty.Prod (Ty.Prod C (Word n)) A) -> option (tySem (Ty.Sum B A)))
    (context : tySem C) (state : tySem A) (target : tySem (Word n)) (result : tySem B) :
  (forall w, @toZ (WordToZ n) w < @toZ (WordToZ n) target ->
    body ((context, w), state) = Some (inr state)) ->
  body ((context, target), state) = Some (inl result) ->
  for_while_run n body context state = Some (inl result).
Proof.
  revert C B A body context state target result.
  induction n; intros C B A body context state target result HBefore HTarget.
  - destruct target as [[] | []]; cbn in HBefore, HTarget |- *.
    + rewrite HTarget. reflexivity.
    + rewrite (HBefore Bit.zero ltac:(change (0 < 1); lia)). exact HTarget.
  - destruct target as [hi lo]. cbn [for_while_run].
    eapply IHn with (target := hi).
    + intros h Hh. apply for_while_run_all_right. intro l.
      apply HBefore. apply search_word_pair_lt_high. exact Hh.
    + eapply IHn with (target := lo).
      * intros l Hl. apply HBefore. apply search_word_pair_lt_low. exact Hl.
      * exact HTarget.
Qed.

Lemma first_fail_run_first_left n {A B : Ty}
    (op : tySem (Word n) -> option (tySem (Ty.Sum A B))) (target : tySem (Word n)) :
  (forall w, @toZ (WordToZ n) w < @toZ (WordToZ n) target ->
    exists b, op w = Some (inr b)) ->
  (exists a, op target = Some (inl a)) ->
  first_fail_run n op = Some target.
Proof.
  intros HBefore [a HTarget]. unfold first_fail_run.
  assert (HSearch : for_while_run n (first_fail_step n op) tt tt = Some (inl target)).
  { eapply for_while_run_first_left with (target := target).
    - intros w Hw. destruct (HBefore w Hw) as [b Hb].
      unfold first_fail_step. cbn [fst snd]. rewrite Hb. reflexivity.
    - unfold first_fail_step. cbn [fst snd]. rewrite HTarget. reflexivity. }
  rewrite HSearch. reflexivity.
Qed.
