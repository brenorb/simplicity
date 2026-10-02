(** Literal recursive Programs.Arith.divPreShift/divPostShift adapters.
    n is the remaining block-word depth; m is the outer vector depth.
    Natural-index casts implement vectorComp's unchanged total word size. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_full_shift_spec C.jet_division_shift_step C.jet_test_value_spec.
Require Import C.jet_predicate_spec.
Require Import C.jet_toZ.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition division_pre_state w := Ty.Prod (Word (S w)) (Word w).
Definition division_post_state w := Ty.Prod (Word w) (Word w).

Definition cast_state_endo (F : nat -> Ty.Ty) p q (e : p = q)
    {term : Alg.Core.Algebra} (f : term (F p) (F p)) : term (F q) (F q) :=
  eq_rect p (fun w => term (F w) (F w)) f q e.

Definition division_pre_branch n m {term : Alg.Core.Algebra} :
  term (division_pre_state (m+n)) (division_pre_state (m+n)) :=
  (Alg.Core.Combinators.drop (@division_leftmost_block n m term >>> @is_zero_word_spec n term)
    &&& Alg.Core.Combinators.iden) >>>
    Bit.cond (@division_pre_shift_step n m term) Alg.Core.Combinators.iden.

Definition division_post_branch n m {term : Alg.Core.Algebra} :
  term (division_post_state (m+n)) (division_post_state (m+n)) :=
  (Alg.Core.Combinators.drop (@division_leftmost_block n m term >>> @is_zero_word_spec n term)
    &&& Alg.Core.Combinators.iden) >>>
    Bit.cond (@division_post_shift_step n m term) Alg.Core.Combinators.iden.

Fixpoint division_pre_shift_spec n m {term : Alg.Core.Algebra} :
  term (division_pre_state (m+n)) (division_pre_state (m+n)) :=
  match n as n return term (division_pre_state (m+n)) (division_pre_state (m+n)) with
  | Datatypes.O => Alg.Core.Combinators.iden
  | Datatypes.S n =>
      @cast_state_endo division_pre_state (S m+n) (m+S n) (eq_sym (Nat.add_succ_r m n)) term
        (@division_pre_branch n (S m) term >>> @division_pre_shift_spec n (S m) term)
  end.

Fixpoint division_post_shift_spec n m {term : Alg.Core.Algebra} :
  term (division_post_state (m+n)) (division_post_state (m+n)) :=
  match n as n return term (division_post_state (m+n)) (division_post_state (m+n)) with
  | Datatypes.O => Alg.Core.Combinators.iden
  | Datatypes.S n =>
      @cast_state_endo division_post_state (S m+n) (m+S n) (eq_sym (Nat.add_succ_r m n)) term
        (@division_post_branch n (S m) term >>> @division_post_shift_spec n (S m) term)
  end.

Lemma division_pre_branch_parametric n m : Alg.Core.Parametric (@division_pre_branch n m).
Proof.
  intros term1 term2 R. unfold division_pre_branch.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [|apply Alg.iden_Parametric].
    apply Alg.drop_Parametric, Alg.comp_Parametric.
    + apply division_leftmost_block_parametric.
    + apply is_zero_word_spec_parametric.
  - apply Bit.cond_Parametric; [apply division_pre_shift_step_parametric|apply Alg.iden_Parametric].
Qed.

Lemma division_post_branch_parametric n m : Alg.Core.Parametric (@division_post_branch n m).
Proof.
  intros term1 term2 R. unfold division_post_branch.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [|apply Alg.iden_Parametric].
    apply Alg.drop_Parametric, Alg.comp_Parametric.
    + apply division_leftmost_block_parametric.
    + apply is_zero_word_spec_parametric.
  - apply Bit.cond_Parametric; [apply division_post_shift_step_parametric|apply Alg.iden_Parametric].
Qed.

Lemma cast_state_endo_parametric F p q (e : p = q)
    (f : forall {term : Alg.Core.Algebra}, term (F p) (F p)) :
  Alg.Core.Parametric (@f) -> Alg.Core.Parametric (fun term => @cast_state_endo F p q e term (@f term)).
Proof. destruct e. intros Hparam. exact Hparam. Qed.

Lemma division_pre_shift_spec_parametric n m : Alg.Core.Parametric (@division_pre_shift_spec n m).
Proof.
  revert m. induction n as [|n IH]; intros m.
  - intros term1 term2 R. apply Alg.iden_Parametric.
  - apply cast_state_endo_parametric. intros term1 term2 R.
    apply Alg.comp_Parametric; [apply division_pre_branch_parametric|apply IH].
Qed.

Lemma division_post_shift_spec_parametric n m : Alg.Core.Parametric (@division_post_shift_spec n m).
Proof.
  revert m. induction n as [|n IH]; intros m.
  - intros term1 term2 R. apply Alg.iden_Parametric.
  - apply cast_state_endo_parametric. intros term1 term2 R.
    apply Alg.comp_Parametric; [apply division_post_branch_parametric|apply IH].
Qed.

Lemma cast_state_value_inverse (F : nat -> Ty.Ty) p q (e : p = q) (v : Ty.tySem (F q)) :
  eq_rect p (fun w => Ty.tySem (F w))
    (eq_rect q (fun w => Ty.tySem (F w)) v p (eq_sym e)) q e = v.
Proof. destruct e; reflexivity. Qed.

Lemma cast_state_endo_core F p q (e : p = q) (f : Ty.Arrow (F p) (F p)) (v : Ty.tySem (F p)) :
  @cast_state_endo F p q e Alg.CoreFunSem f
    (eq_rect p (fun w => Ty.tySem (F w)) v q e) =
    eq_rect p (fun w => Ty.tySem (F w)) (f v) q e.
Proof. destruct e; reflexivity. Qed.

Lemma cast_pre_state_values p q (e : p = q) (v : Ty.tySem (division_pre_state p)) :
  let cast := eq_rect p (fun w => Ty.tySem (division_pre_state w)) v q e in
  @toZ (WordToZ (S q)) (fst cast) = @toZ (WordToZ (S p)) (fst v) /\
  @toZ (WordToZ q) (snd cast) = @toZ (WordToZ p) (snd v).
Proof. destruct e; split; reflexivity. Qed.

Lemma cast_post_state_values p q (e : p = q) (v : Ty.tySem (division_post_state p)) :
  let cast := eq_rect p (fun w => Ty.tySem (division_post_state w)) v q e in
  @toZ (WordToZ q) (fst cast) = @toZ (WordToZ p) (fst v) /\
  @toZ (WordToZ q) (snd cast) = @toZ (WordToZ p) (snd v).
Proof. destruct e; split; reflexivity. Qed.

Lemma cast_pre_state_endo_values p q (e : p = q)
    (f : Ty.Arrow (division_pre_state p) (division_pre_state p))
    (v : Ty.tySem (division_pre_state q)) :
  let u := eq_rect q (fun w => Ty.tySem (division_pre_state w)) v p (eq_sym e) in
  let result := @cast_state_endo division_pre_state p q e Alg.CoreFunSem f v in
  @toZ (WordToZ (S q)) (fst result) = @toZ (WordToZ (S p)) (fst (f u)) /\
  @toZ (WordToZ q) (snd result) = @toZ (WordToZ p) (snd (f u)).
Proof. destruct e; split; reflexivity. Qed.

Lemma cast_post_state_endo_values p q (e : p = q)
    (f : Ty.Arrow (division_post_state p) (division_post_state p))
    (v : Ty.tySem (division_post_state q)) :
  let u := eq_rect q (fun w => Ty.tySem (division_post_state w)) v p (eq_sym e) in
  let result := @cast_state_endo division_post_state p q e Alg.CoreFunSem f v in
  @toZ (WordToZ q) (fst result) = @toZ (WordToZ p) (fst (f u)) /\
  @toZ (WordToZ q) (snd result) = @toZ (WordToZ p) (snd (f u)).
Proof. destruct e; split; reflexivity. Qed.

Lemma division_pre_branch_core n m (v : Ty.tySem (division_pre_state (m+n))) :
  @division_pre_branch n m Alg.CoreFunSem v =
  match @is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n m Alg.CoreFunSem (snd v)) with
  | inl _ => v
  | inr _ => @division_pre_shift_step n m Alg.CoreFunSem v
  end.
Proof.
  destruct v as [a b]. unfold division_pre_branch.
  cbn -[is_zero_word_spec division_leftmost_block division_pre_shift_step].
  destruct (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n m Alg.CoreFunSem b)) as [[] | []]; reflexivity.
Qed.

Lemma division_pre_branch_scale n m (a : Ty.tySem (Word (S (S m+n))))
    (b : Ty.tySem (Word (S m+n))) :
  word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) b * word_modulus (S n) ->
  @toZ (WordToZ (S (S m+n))) a < @toZ (WordToZ (S m+n)) b * word_modulus (S m+n) ->
  let result := @division_pre_branch n (S m) Alg.CoreFunSem (a,b) in
  exists k, 0 < k /\
    @toZ (WordToZ (S (S m+n))) (fst result) = @toZ (WordToZ (S (S m+n))) a * k /\
    @toZ (WordToZ (S m+n)) (snd result) = @toZ (WordToZ (S m+n)) b * k /\
    word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) (snd result) * word_modulus n /\
    @toZ (WordToZ (S (S m+n))) (fst result) <
      @toZ (WordToZ (S m+n)) (snd result) * word_modulus (S m+n).
Proof.
  intros Hlower Hnum. cbn zeta.
  replace (@division_pre_branch n (S m) Alg.CoreFunSem (a,b)) with
    (match @is_zero_word_spec n Alg.CoreFunSem
      (@division_leftmost_block n (S m) Alg.CoreFunSem b) with
     | inl _ => (a,b)
     | inr _ => @division_pre_shift_step n (S m) Alg.CoreFunSem (a,b)
     end) by (symmetry; apply division_pre_branch_core).
  destruct (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n (S m) Alg.CoreFunSem b)) as [[] | []] eqn:HG.
  - pose proof (division_nonzero_guard_bound n m b ltac:(rewrite HG; reflexivity)) as Hb.
    exists 1. cbn [fst snd]. repeat split; try lia; try ring; assumption.
  - pose proof (division_zero_guard_bound n m b ltac:(rewrite HG; reflexivity)) as Hb.
    destruct (division_pre_shift_step_value n (S m) a b Hb Hnum) as [HA [HB HN]].
    exists (word_modulus n). split; [apply word_modulus_positive|].
    split; [exact HA|]. split; [exact HB|]. split; [|exact HN].
    rewrite word_modulus_S in Hlower.
    eapply Z.le_trans; [exact Hlower|]. apply Z.eq_le_incl.
    transitivity ((@toZ (WordToZ (S m+n)) b * word_modulus n) * word_modulus n); [ring|].
    exact (f_equal (fun z => z * word_modulus n) (eq_sym HB)).
Qed.

Lemma division_pre_shift_succ_values n m (v : Ty.tySem (division_pre_state (m+S n))) :
  let e := eq_sym (Nat.add_succ_r m n) in
  let u := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_pre_state w)) v (S m+n)%nat (eq_sym e) in
  let rec := @division_pre_shift_spec n (S m) Alg.CoreFunSem
    (@division_pre_branch n (S m) Alg.CoreFunSem u) in
  let result := @division_pre_shift_spec (S n) m Alg.CoreFunSem v in
  @toZ (WordToZ (S (m+S n))) (fst result) = @toZ (WordToZ (S (S m+n))) (fst rec) /\
  @toZ (WordToZ (m+S n)) (snd result) = @toZ (WordToZ (S m+n)) (snd rec).
Proof. apply cast_pre_state_endo_values. Qed.

Lemma numeric_lt_product_transport x x' y y' c c' :
  x = x' -> y = y' -> c = c' -> x' < y' * c' -> x < y * c.
Proof. intros -> -> ->; trivial. Qed.

Lemma division_pre_shift_normalizes n m (v : Ty.tySem (division_pre_state (m+n))) :
  word_modulus (m+n) <= @toZ (WordToZ (m+n)) (snd v) * word_modulus n ->
  @toZ (WordToZ (S (m+n))) (fst v) <
    @toZ (WordToZ (m+n)) (snd v) * word_modulus (m+n) ->
  let result := @division_pre_shift_spec n m Alg.CoreFunSem v in
  exists k, 0 < k /\
    @toZ (WordToZ (S (m+n))) (fst result) = @toZ (WordToZ (S (m+n))) (fst v) * k /\
    @toZ (WordToZ (m+n)) (snd result) = @toZ (WordToZ (m+n)) (snd v) * k /\
    word_modulus (m+n) <= 2 * @toZ (WordToZ (m+n)) (snd result) /\
    @toZ (WordToZ (S (m+n))) (fst result) <
      @toZ (WordToZ (m+n)) (snd result) * word_modulus (m+n).
Proof.
  revert m v. induction n as [|n IH]; intros m v Hlower Hnum.
  - exists 1. change (word_modulus 0) with 2 in Hlower.
    cbn -[toZ word_modulus Z.mul]. repeat split; try ring; try lia; assumption.
  - cbn zeta.
    set (e := eq_sym (Nat.add_succ_r m n)).
    set (u := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_pre_state w)) v (S m+n)%nat (eq_sym e)).
    pose proof (division_pre_shift_succ_values n m v) as Hsucc.
    change (@toZ (WordToZ (S (m+S n)))
      (fst (@division_pre_shift_spec (S n) m Alg.CoreFunSem v)) =
      @toZ (WordToZ (S (S m+n)))
        (fst (@division_pre_shift_spec n (S m) Alg.CoreFunSem
          (@division_pre_branch n (S m) Alg.CoreFunSem u))) /\
      @toZ (WordToZ (m+S n))
      (snd (@division_pre_shift_spec (S n) m Alg.CoreFunSem v)) =
      @toZ (WordToZ (S m+n))
        (snd (@division_pre_shift_spec n (S m) Alg.CoreFunSem
          (@division_pre_branch n (S m) Alg.CoreFunSem u)))) in Hsucc.
    pose proof (cast_pre_state_values (m+S n) (S m+n) (eq_sym e) v) as Hinput.
    fold u in Hinput. cbn zeta in Hinput.
    destruct Hinput as [HIa HIb]. destruct Hsucc as [HSa HSb].
    pose proof (f_equal word_modulus e) as HM.
    destruct u as [a b]. cbn [fst snd] in HIa, HIb.
    assert (HLu : word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) b * word_modulus (S n)).
    { eapply Z.le_trans; [apply Z.eq_le_incl; exact HM|].
      eapply Z.le_trans; [exact Hlower|]. apply Z.eq_le_incl.
      exact (f_equal (fun z => z * word_modulus (S n)) (eq_sym HIb)). }
    assert (HNu : @toZ (WordToZ (S (S m+n))) a < @toZ (WordToZ (S m+n)) b * word_modulus (S m+n)).
    { eapply numeric_lt_product_transport; [exact HIa|exact HIb|exact HM|exact Hnum]. }
    destruct (division_pre_branch_scale n m a b HLu HNu)
      as [k [HK [HA [HB [HL1 HN1]]]]].
    destruct (IH (S m) (@division_pre_branch n (S m) Alg.CoreFunSem (a,b)) HL1 HN1)
      as [j [HJ [HAj [HBj [HLj HNj]]]]].
    exists (k*j). split; [nia|].
    split.
    + etransitivity; [exact HSa|]. etransitivity; [exact HAj|].
      transitivity ((@toZ (WordToZ (S (S m+n))) a * k) * j).
      * exact (f_equal (fun z => z * j) HA).
      * rewrite HIa. ring.
    + split.
      * etransitivity; [exact HSb|]. etransitivity; [exact HBj|].
        transitivity ((@toZ (WordToZ (S m+n)) b * k) * j).
        -- exact (f_equal (fun z => z * j) HB).
        -- rewrite HIb. ring.
      * split.
        -- eapply Z.le_trans; [apply Z.eq_le_incl; symmetry; exact HM|].
           eapply Z.le_trans; [exact HLj|]. apply Z.eq_le_incl.
           exact (f_equal (fun z => 2*z) (eq_sym HSb)).
        -- eapply numeric_lt_product_transport; [exact HSa|exact HSb|symmetry; exact HM|exact HNj].
Qed.

Lemma division_post_branch_core n m (v : Ty.tySem (division_post_state (m+n))) :
  @division_post_branch n m Alg.CoreFunSem v =
  match @is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n m Alg.CoreFunSem (snd v)) with
  | inl _ => v
  | inr _ => @division_post_shift_step n m Alg.CoreFunSem v
  end.
Proof.
  destruct v as [a b]. unfold division_post_branch.
  cbn -[is_zero_word_spec division_leftmost_block division_post_shift_step].
  destruct (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n m Alg.CoreFunSem b)) as [[] | []]; reflexivity.
Qed.

Lemma division_post_branch_scale n m (a b : Ty.tySem (Word (S m+n))) :
  word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) b * word_modulus (S n) ->
  let result := @division_post_branch n (S m) Alg.CoreFunSem (a,b) in
  exists k, 0 < k /\
    @toZ (WordToZ (S m+n)) (fst result) = @toZ (WordToZ (S m+n)) a / k /\
    @toZ (WordToZ (S m+n)) (snd result) = @toZ (WordToZ (S m+n)) b * k /\
    word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) (snd result) * word_modulus n.
Proof.
  intros Hlower. cbn zeta.
  replace (@division_post_branch n (S m) Alg.CoreFunSem (a,b)) with
    (match @is_zero_word_spec n Alg.CoreFunSem
      (@division_leftmost_block n (S m) Alg.CoreFunSem b) with
     | inl _ => (a,b)
     | inr _ => @division_post_shift_step n (S m) Alg.CoreFunSem (a,b)
     end) by (symmetry; apply division_post_branch_core).
  destruct (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n (S m) Alg.CoreFunSem b)) as [[] | []] eqn:HG.
  - pose proof (division_nonzero_guard_bound n m b ltac:(rewrite HG; reflexivity)) as Hb.
    exists 1. cbn [fst snd]. rewrite Z.div_1_r.
    repeat split; try lia; try ring; assumption.
  - pose proof (division_zero_guard_bound n m b ltac:(rewrite HG; reflexivity)) as Hb.
    destruct (division_post_shift_step_value n (S m) a b Hb) as [HA HB].
    exists (word_modulus n). split; [apply word_modulus_positive|].
    split; [exact HA|]. split; [exact HB|].
    rewrite word_modulus_S in Hlower.
    eapply Z.le_trans; [exact Hlower|]. apply Z.eq_le_incl.
    transitivity ((@toZ (WordToZ (S m+n)) b * word_modulus n) * word_modulus n); [ring|].
    exact (f_equal (fun z => z * word_modulus n) (eq_sym HB)).
Qed.

Lemma division_post_shift_succ_values n m (v : Ty.tySem (division_post_state (m+S n))) :
  let e := eq_sym (Nat.add_succ_r m n) in
  let u := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_post_state w)) v (S m+n)%nat (eq_sym e) in
  let rec := @division_post_shift_spec n (S m) Alg.CoreFunSem
    (@division_post_branch n (S m) Alg.CoreFunSem u) in
  let result := @division_post_shift_spec (S n) m Alg.CoreFunSem v in
  @toZ (WordToZ (m+S n)) (fst result) = @toZ (WordToZ (S m+n)) (fst rec) /\
  @toZ (WordToZ (m+S n)) (snd result) = @toZ (WordToZ (S m+n)) (snd rec).
Proof. apply cast_post_state_endo_values. Qed.

Lemma division_post_shift_normalizes n m (v : Ty.tySem (division_post_state (m+n))) :
  word_modulus (m+n) <= @toZ (WordToZ (m+n)) (snd v) * word_modulus n ->
  let result := @division_post_shift_spec n m Alg.CoreFunSem v in
  exists k, 0 < k /\
    @toZ (WordToZ (m+n)) (fst result) = @toZ (WordToZ (m+n)) (fst v) / k /\
    @toZ (WordToZ (m+n)) (snd result) = @toZ (WordToZ (m+n)) (snd v) * k /\
    word_modulus (m+n) <= 2 * @toZ (WordToZ (m+n)) (snd result).
Proof.
  revert m v. induction n as [|n IH]; intros m v Hlower.
  - exists 1. change (word_modulus 0) with 2 in Hlower.
    cbn -[toZ word_modulus Z.mul Z.div]. rewrite Z.div_1_r.
    repeat split; try ring; lia.
  - cbn zeta.
    set (e := eq_sym (Nat.add_succ_r m n)).
    set (u := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_post_state w)) v (S m+n)%nat (eq_sym e)).
    pose proof (division_post_shift_succ_values n m v) as Hsucc.
    change (@toZ (WordToZ (m+S n))
      (fst (@division_post_shift_spec (S n) m Alg.CoreFunSem v)) =
      @toZ (WordToZ (S m+n))
        (fst (@division_post_shift_spec n (S m) Alg.CoreFunSem
          (@division_post_branch n (S m) Alg.CoreFunSem u))) /\
      @toZ (WordToZ (m+S n))
      (snd (@division_post_shift_spec (S n) m Alg.CoreFunSem v)) =
      @toZ (WordToZ (S m+n))
        (snd (@division_post_shift_spec n (S m) Alg.CoreFunSem
          (@division_post_branch n (S m) Alg.CoreFunSem u)))) in Hsucc.
    pose proof (cast_post_state_values (m+S n) (S m+n) (eq_sym e) v) as Hinput.
    fold u in Hinput. cbn zeta in Hinput.
    destruct Hinput as [HIa HIb]. destruct Hsucc as [HSa HSb].
    pose proof (f_equal word_modulus e) as HM.
    destruct u as [a b]. cbn [fst snd] in HIa, HIb.
    assert (HLu : word_modulus (S m+n) <= @toZ (WordToZ (S m+n)) b * word_modulus (S n)).
    { eapply Z.le_trans; [apply Z.eq_le_incl; exact HM|].
      eapply Z.le_trans; [exact Hlower|]. apply Z.eq_le_incl.
      exact (f_equal (fun z => z * word_modulus (S n)) (eq_sym HIb)). }
    destruct (division_post_branch_scale n m a b HLu) as [k [HK [HA [HB HL1]]]].
    destruct (IH (S m) (@division_post_branch n (S m) Alg.CoreFunSem (a,b)) HL1)
      as [j [HJ [HAj [HBj HLj]]]].
    exists (k*j). split; [nia|]. split.
    + etransitivity; [exact HSa|]. etransitivity; [exact HAj|].
      transitivity ((@toZ (WordToZ (S m+n)) a / k) / j).
      * exact (f_equal (fun z => z / j) HA).
      * rewrite HIa. apply Z.div_div; lia.
    + split.
      * etransitivity; [exact HSb|]. etransitivity; [exact HBj|].
        transitivity ((@toZ (WordToZ (S m+n)) b * k) * j).
        -- exact (f_equal (fun z => z * j) HB).
        -- rewrite HIb. ring.
      * eapply Z.le_trans; [apply Z.eq_le_incl; symmetry; exact HM|].
        eapply Z.le_trans; [exact HLj|]. apply Z.eq_le_incl.
        exact (f_equal (fun z => 2*z) (eq_sym HSb)).
Qed.

Lemma division_branch_same_denominator n m
    (a : Ty.tySem (Word (S (m+n)))) (r b : Ty.tySem (Word (m+n))) :
  snd (@division_pre_branch n m Alg.CoreFunSem (a,b)) =
    snd (@division_post_branch n m Alg.CoreFunSem (r,b)).
Proof.
  unfold division_pre_branch, division_post_branch.
  cbn -[is_zero_word_spec division_leftmost_block division_pre_shift_step division_post_shift_step].
  destruct (@is_zero_word_spec n Alg.CoreFunSem
    (@division_leftmost_block n m Alg.CoreFunSem b)) as [[] | []]; [reflexivity|].
  change (snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt)) =
    snd (@full_left_word_spec n m Alg.CoreFunSem (b,@Word.zero n Alg.CoreFunSem tt))).
  reflexivity.
Qed.

Lemma division_pre_post_same_denominator n m
    (a : Ty.tySem (Word (S (m+n)))) (r b : Ty.tySem (Word (m+n))) :
  @toZ (WordToZ (m+n)) (snd (@division_pre_shift_spec n m Alg.CoreFunSem (a,b))) =
  @toZ (WordToZ (m+n)) (snd (@division_post_shift_spec n m Alg.CoreFunSem (r,b))).
Proof.
  revert m a r b. induction n as [|n IH]; intros m a r b.
  - reflexivity.
  - set (e := eq_sym (Nat.add_succ_r m n)).
    set (up := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_pre_state w)) (a,b)
      (S m+n)%nat (eq_sym e)).
    set (ur := eq_rect (m+S n)%nat (fun w => Ty.tySem (division_post_state w)) (r,b)
      (S m+n)%nat (eq_sym e)).
    destruct (division_pre_shift_succ_values n m (a,b)) as [_ HP].
    change (@toZ (WordToZ (m+S n))
      (snd (@division_pre_shift_spec (S n) m Alg.CoreFunSem (a,b))) =
      @toZ (WordToZ (S m+n)) (snd (@division_pre_shift_spec n (S m) Alg.CoreFunSem
        (@division_pre_branch n (S m) Alg.CoreFunSem up)))) in HP.
    destruct (division_post_shift_succ_values n m (r,b)) as [_ HR].
    change (@toZ (WordToZ (m+S n))
      (snd (@division_post_shift_spec (S n) m Alg.CoreFunSem (r,b))) =
      @toZ (WordToZ (S m+n)) (snd (@division_post_shift_spec n (S m) Alg.CoreFunSem
        (@division_post_branch n (S m) Alg.CoreFunSem ur)))) in HR.
    destruct (cast_pre_state_values (m+S n) (S m+n) (eq_sym e) (a,b)) as [_ HBp].
    destruct (cast_post_state_values (m+S n) (S m+n) (eq_sym e) (r,b)) as [_ HBr].
    change (@toZ (WordToZ (S m+n)) (snd up) = @toZ (WordToZ (m+S n)) b) in HBp.
    change (@toZ (WordToZ (S m+n)) (snd ur) = @toZ (WordToZ (m+S n)) b) in HBr.
    destruct up as [ap bp]. destruct ur as [rp br]. cbn [snd] in HBp, HBr.
    assert (HB : br = bp).
    { apply (toZ_injective (WordToZ (S m+n))). etransitivity; [exact HBr|symmetry; exact HBp]. }
    subst br.
    pose proof (division_branch_same_denominator n (S m) ap rp bp) as HBnext.
    destruct (@division_pre_branch n (S m) Alg.CoreFunSem (ap,bp)) as [ap' bp'] eqn:HPbranch.
    destruct (@division_post_branch n (S m) Alg.CoreFunSem (rp,bp)) as [rp' br'] eqn:HRbranch.
    cbn [snd] in HBnext. subst br'.
    etransitivity; [exact HP|]. etransitivity; [apply IH|symmetry; exact HR].
Qed.

Lemma division_normalization_pair n m (a : Ty.tySem (Word (S (m+n))))
    (r b : Ty.tySem (Word (m+n))) :
  word_modulus (m+n) <= @toZ (WordToZ (m+n)) b * word_modulus n ->
  @toZ (WordToZ (S (m+n))) a < @toZ (WordToZ (m+n)) b * word_modulus (m+n) ->
  let pre := @division_pre_shift_spec n m Alg.CoreFunSem (a,b) in
  let post := @division_post_shift_spec n m Alg.CoreFunSem (r,b) in
  exists k, 0 < k /\
    @toZ (WordToZ (S (m+n))) (fst pre) = @toZ (WordToZ (S (m+n))) a * k /\
    @toZ (WordToZ (m+n)) (snd pre) = @toZ (WordToZ (m+n)) b * k /\
    @toZ (WordToZ (m+n)) (fst post) = @toZ (WordToZ (m+n)) r / k /\
    @toZ (WordToZ (m+n)) (snd post) = @toZ (WordToZ (m+n)) (snd pre) /\
    word_modulus (m+n) <= 2 * @toZ (WordToZ (m+n)) (snd pre) /\
    @toZ (WordToZ (S (m+n))) (fst pre) <
      @toZ (WordToZ (m+n)) (snd pre) * word_modulus (m+n).
Proof.
  intros Hlower Hnum. cbn zeta.
  destruct (division_pre_shift_normalizes n m (a,b) Hlower Hnum)
    as [k [HK [HA [HB [HL HN]]]]].
  destruct (division_post_shift_normalizes n m (r,b) Hlower)
    as [j [HJ [HR [HBj HLj]]]].
  pose proof (division_pre_post_same_denominator n m a r b) as HD.
  pose proof (word_modulus_positive n) as HP.
  pose proof (word_modulus_positive (m+n)) as HM.
  assert (HBpos : 0 < @toZ (WordToZ (m+n)) b) by nia.
  assert (HE : @toZ (WordToZ (m+n)) b * k = @toZ (WordToZ (m+n)) b * j).
  { etransitivity; [symmetry; exact HB|]. etransitivity; [exact HD|exact HBj]. }
  assert (Hkj : k = j) by nia. subst j.
  exists k. repeat split; try assumption. symmetry; exact HD.
Qed.

Lemma division_plain_input_normalization n (a r b : Ty.tySem (Word n)) :
  0 < @toZ (WordToZ n) b ->
  let pre := @division_pre_shift_spec n 0 Alg.CoreFunSem ((@Word.zero n Alg.CoreFunSem tt,a),b) in
  let post := @division_post_shift_spec n 0 Alg.CoreFunSem (r,b) in
  exists k, 0 < k /\
    @toZ (WordToZ (S n)) (fst pre) = @toZ (WordToZ n) a * k /\
    @toZ (WordToZ n) (snd pre) = @toZ (WordToZ n) b * k /\
    @toZ (WordToZ n) (fst post) = @toZ (WordToZ n) r / k /\
    @toZ (WordToZ n) (snd post) = @toZ (WordToZ n) (snd pre) /\
    word_modulus n <= 2 * @toZ (WordToZ n) (snd pre) /\
    @toZ (WordToZ (S n)) (fst pre) < @toZ (WordToZ n) (snd pre) * word_modulus n.
Proof.
  intros HBpos. cbn zeta.
  pose proof (word_value_bounds n a) as HA.
  pose proof (word_modulus_positive n) as HM.
  assert (HI : @toZ (WordToZ (S n)) (@Word.zero n Alg.CoreFunSem tt,a) = @toZ (WordToZ n) a).
  { change (@toZ (WordToZ n) (@Word.zero n Alg.CoreFunSem tt) * word_modulus n +
      @toZ (WordToZ n) a = @toZ (WordToZ n) a).
    rewrite Word.zero_correct; ring. }
  assert (HL : word_modulus n <= @toZ (WordToZ n) b * word_modulus n) by nia.
  assert (HN : @toZ (WordToZ (S n)) (@Word.zero n Alg.CoreFunSem tt,a) <
    @toZ (WordToZ n) b * word_modulus n).
  { rewrite HI. nia. }
  destruct (division_normalization_pair n 0 (@Word.zero n Alg.CoreFunSem tt,a) r b HL HN)
    as [k [HK [HNP [HDP [HR [HD [Hlead Hbound]]]]]]].
  exists k. split; [exact HK|]. split.
  - etransitivity; [exact HNP|]. exact (f_equal (fun z => z*k) HI).
  - repeat split; assumption.
Qed.
