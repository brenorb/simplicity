(** Context-preserving finite fold for canonical keyed transaction programs. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word C.jet_forWhile_spec C.jet_forWhile_seq C.jet_forWhile_fold.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem for_while_run_fold_list_context {X : Type} {C A : Ty} n (xs : list X)
    (step : tySem A -> X -> tySem A) (initial : tySem A) (context : tySem C)
    (body : tySem (Ty.Prod (Ty.Prod C (Word n)) A) ->
      option (tySem (Ty.Sum A A))) :
  Z.of_nat (length xs) < wsize n ->
  (forall w a, body ((context, w), a) =
    Some (match nth_error xs (Z.to_nat (wz n w)) with
          | Some x => inr (step a x) | None => inl a end)) ->
  for_while_run n body context initial = Some (inl (fold_left step xs initial)).
Proof.
  intros Hlen Hbody.
  set (prefix := fun z : Z => fold_left step (firstn (Z.to_nat z) xs) initial).
  assert (H0 : prefix 0 = initial) by reflexivity.
  assert (HL : prefix (Z.of_nat (length xs)) = fold_left step xs initial).
  { unfold prefix. rewrite Nat2Z.id, firstn_all. reflexivity. }
  rewrite <- HL. rewrite <- H0 at 1.
  refine (@for_while_run_seq_left C A A prefix n 0 (Z.of_nat (length xs))
    (prefix (Z.of_nat (length xs))) body context _ _ _).
  - lia.
  - intros w Hw. rewrite Hbody.
    destruct (nth_error xs (Z.to_nat (wz n w))) as [x|] eqn:HX.
    + f_equal. f_equal. unfold prefix. replace (0 + wz n w) with (wz n w) by lia.
      replace (0 + wz n w + 1) with (wz n w + 1) by lia.
      assert (HN : Z.to_nat (wz n w + 1) = S (Z.to_nat (wz n w))).
      { pose proof (wz_range n w). lia. }
      rewrite HN. symmetry. apply fold_left_firstn_next. exact HX.
    + apply nth_error_None in HX. pose proof (wz_range n w). exfalso. lia.
  - intros w Hw. rewrite Hbody.
    assert (HN : Z.to_nat (wz n w) = length xs) by lia.
    assert (HX : nth_error xs (length xs) = None) by (apply nth_error_None; lia).
    rewrite HN, HX. reflexivity.
Qed.
