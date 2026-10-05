(** Literal ports of Programs.Word.bufferSnoc and of
    Programs.Sha256.mkLibAssert.ctx8Add1 / ctx8Addn, with their option
    semantics as a byte-list model:  adding bytes appends them to the
    buffered bytes, every completed 64-byte block is compressed with
    hashBlock and counted, and the result exists exactly when the final
    compression count stays below 2^55. *)
From Coq Require Import ZArith List Lia PeanoNat.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_assertion_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_increment_spec C.jet_increment_wide_word C.jet_order_spec C.jet_sha256_count_assertion.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Fixpoint buffer_list (X : Ty.Ty) (depth : nat) : Ty.tySem (buffer_type X depth) -> list (Ty.tySem X) :=
  match depth return Ty.tySem (buffer_type X depth) -> list (Ty.tySem X) with
  | O => fun x => match x with inl _ => [] | inr y => [y] end
  | S d => fun x =>
      match fst x with inl _ => [] | inr v => vector_values X (S d) v end ++ buffer_list X d (snd x)
  end.

Lemma buffer_list_empty X depth : buffer_list X depth (buffer_empty_value X depth) = [].
Proof. induction depth; [reflexivity|]. cbn [buffer_list buffer_empty_value fst snd]. exact IHdepth. Qed.

(** bufferSnoc :: Buffer x v b -> term (b, x) (Either v b) *)
Fixpoint buffer_snoc_spec (X : Ty.Ty) (depth : nat) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (buffer_type X depth) X) (Ty.Sum (Vector X (S depth)) (buffer_type X depth)) :=
  match depth with
  | O => AC.case (AC.injr (AC.injr (AC.drop AC.iden))) (AC.injl AC.iden)
  | S d =>
      AC.comp
        (AC.pair (AC.comp (AC.pair (AC.take (AC.drop AC.iden)) (AC.drop AC.iden)) (buffer_snoc_spec X d))
                 (AC.take (AC.take AC.iden)))
        (AC.case
          (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
            (AC.case (AC.injr (AC.pair (AC.injr (AC.drop AC.iden)) (buffer_empty_spec X d _)))
                     (AC.injl AC.iden)))
          (AC.injr (AC.pair (AC.drop AC.iden) (AC.take AC.iden))))
  end.

Lemma buffer_snoc_spec_parametric X depth : Alg.Core.Parametric (@buffer_snoc_spec X depth).
Proof.
  intros alg1 alg2 R. induction depth; cbn [buffer_snoc_spec];
    repeat first [exact IHdepth | apply buffer_empty_spec_parametric
      | apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.case_Parametric
      | apply Alg.injl_Parametric | apply Alg.injr_Parametric | apply Alg.take_Parametric
      | apply Alg.drop_Parametric | apply Alg.iden_Parametric | apply Alg.unit_Parametric].
Qed.

Lemma buffer_snoc_value X depth (b : Ty.tySem (buffer_type X depth)) (x : Ty.tySem X) :
  match @buffer_snoc_spec X depth Alg.CoreFunSem (b, x) with
  | inl v => vector_values X (S depth) v = buffer_list X depth b ++ [x]
  | inr b' => buffer_list X depth b' = buffer_list X depth b ++ [x]
  end.
Proof.
  induction depth.
  - destruct b as [[]|y]; reflexivity.
  - destruct b as [sv b0]. specialize (IHdepth b0).
    change (@buffer_snoc_spec X (S depth) Alg.CoreFunSem (sv, b0, x)) with
      (match @buffer_snoc_spec X depth Alg.CoreFunSem (b0, x) with
       | inl v1 => match sv with
                   | inl u => inr (inr v1, @buffer_empty_spec X depth (Ty.Prod Ty.Unit (Vector X (S depth))) Alg.CoreFunSem
                         ((u, v1) : Ty.tySem (Ty.Prod Ty.Unit (Vector X (S depth)))))
                   | inr v0 => inl (v0, v1)
                   end
       | inr b'' => inr (sv, b'')
       end).
    destruct (@buffer_snoc_spec X depth Alg.CoreFunSem (b0, x)) as [v1|b''].
    + destruct sv as [[]|v0].
      * rewrite buffer_empty_spec_value.
        cbn [buffer_list fst snd]. rewrite buffer_list_empty, app_nil_r.
        cbn [app]. exact IHdepth.
      * cbn [buffer_list fst snd]. change (vector_values X (S (S depth)) (v0, v1)) with
          (vector_values X (S depth) v0 ++ vector_values X (S depth) v1).
        rewrite IHdepth, app_assoc. reflexivity.
    + cbn [buffer_list fst snd]. rewrite IHdepth, app_assoc. reflexivity.
Qed.

(** * Option semantics of the assertion algebra, combinator by combinator *)
Notation optalg := (Alg.AssertionSem option_Monad_Zero).

Lemma opt_core {A B : Ty.Ty} (t : forall alg : Alg.Core.Algebra, @Alg.Core.domain alg A B)
    (Ht : Alg.Core.Parametric t) (a : Ty.tySem A) :
  t (Alg.Assertion.toCore optalg) a = Some (t Alg.CoreFunSem a).
Proof. exact (Alg.CoreSem_initial (M := option_CIMonad) Ht a). Qed.

Lemma opt_comp {A B C : Ty.Ty} (s : @Alg.Assertion.domain optalg A B) (t : @Alg.Assertion.domain optalg B C) a :
  @AC.comp A B C (Alg.Assertion.toCore optalg) s t a = match s a with Some b => t b | None => None end.
Proof. cbv. destruct (s a); reflexivity. Qed.

Lemma opt_pair {A B C : Ty.Ty} (s : @Alg.Assertion.domain optalg A B) (t : @Alg.Assertion.domain optalg A C) a :
  @AC.pair A B C (Alg.Assertion.toCore optalg) s t a =
    match s a, t a with Some b, Some c => Some (b, c) | _, _ => None end.
Proof. cbv. destruct (s a), (t a); reflexivity. Qed.

Lemma opt_case {A B C D : Ty.Ty} (s : @Alg.Assertion.domain optalg (Ty.Prod A C) D)
    (t : @Alg.Assertion.domain optalg (Ty.Prod B C) D) (p : Ty.tySem (Ty.Prod (Ty.Sum A B) C)) :
  @AC.case A B C D (Alg.Assertion.toCore optalg) s t p =
    match fst p with inl a => s (a, snd p) | inr b => t (b, snd p) end.
Proof. destruct p as [[a|b] c]; reflexivity. Qed.
Lemma opt_take {A B C : Ty.Ty} (t : @Alg.Assertion.domain optalg A C) (p : Ty.tySem (Ty.Prod A B)) :
  @AC.take A B C (Alg.Assertion.toCore optalg) t p = t (fst p).
Proof. destruct p; reflexivity. Qed.
Lemma opt_drop {A B C : Ty.Ty} (t : @Alg.Assertion.domain optalg B C) (p : Ty.tySem (Ty.Prod A B)) :
  @AC.drop A B C (Alg.Assertion.toCore optalg) t p = t (snd p).
Proof. destruct p; reflexivity. Qed.
Lemma opt_iden {A : Ty.Ty} (a : Ty.tySem A) : @AC.iden A (Alg.Assertion.toCore optalg) a = Some a.
Proof. reflexivity. Qed.
Lemma opt_unit {A : Ty.Ty} (a : Ty.tySem A) : @AC.unit A (Alg.Assertion.toCore optalg) a = Some tt.
Proof. reflexivity. Qed.
Lemma opt_assertl_l {A B C D : Ty.Ty} (s : @Alg.Assertion.domain optalg (Ty.Prod A C) D) h a c :
  @Alg.Assertion.Combinators.assertl A B C D optalg s h (inl a, c) = s (a, c).
Proof. reflexivity. Qed.
Lemma opt_assertl_r {A B C D : Ty.Ty} (s : @Alg.Assertion.domain optalg (Ty.Prod A C) D) h (b : Ty.tySem B) c :
  @Alg.Assertion.Combinators.assertl A B C D optalg s h (inr b, c) = None.
Proof. reflexivity. Qed.

(** * ctx8Add1 *)
Definition ctx8_buf := buffer_type (Word 3) 5.
Definition ctx8_tail := Ty.Prod (Word 6) (Word 8).

(** (ooh &&& ih >>> buffer63Snoc) &&& oih *)
Definition ctx8_add1_snoc {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod sha256_ctx8_type (Word 3)) (Ty.Prod (Ty.Sum (Word 9) ctx8_buf) ctx8_tail) :=
  AC.pair
    (AC.comp (AC.pair (AC.take (AC.take AC.iden)) (AC.drop AC.iden)) (buffer_snoc_spec (Word 3) 5))
    (AC.take (AC.drop AC.iden)).

(** (unit >>> buffer63Empty) &&& ((drop (take (increment word64) >>> assertl ih cmrFail0))
      &&& (iih &&& oh >>> hashBlock)) *)
Definition ctx8_add1_full {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod (Word 9) ctx8_tail) sha256_ctx8_type :=
  AC.pair (AC.comp AC.unit (buffer_empty_spec (Word 3) 5 Ty.Unit))
    (AC.pair
      (AC.drop (AC.comp (AC.take (@increment_word_spec (Alg.Assertion.toCore term) 6))
        (@Alg.Assertion.Combinators.assertl Ty.Unit Ty.Unit (Word 6) (Word 6) term
          (@AC.drop Ty.Unit (Word 6) (Word 6) (Alg.Assertion.toCore term) (@AC.iden (Word 6) (Alg.Assertion.toCore term)))
          assertion_cmr_fail0)))
      (AC.comp (AC.pair (AC.drop (AC.drop AC.iden)) (AC.take AC.iden)) Simplicity.SHA256.hashBlock)).

Definition ctx8_add1_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Word 3)) sha256_ctx8_type :=
  AC.comp (@ctx8_add1_snoc (Alg.Assertion.toCore term))
    (AC.comp (@AC.case _ _ _ _ (Alg.Assertion.toCore term) (@ctx8_add1_full term) AC.iden)
      (AC.comp (@AC.pair _ _ _ (Alg.Assertion.toCore term) (@sha256_count_assertion_spec term) AC.iden)
        (AC.drop AC.iden))).

Definition ctx8_limit : Z := 36028797018963968.

Definition ctx8_add1_model (c : Ty.tySem sha256_ctx8_type) (x : Ty.tySem (Word 3)) :
    option (Ty.tySem sha256_ctx8_type) :=
  let '(buf, (count, h)) := c in
  match @buffer_snoc_spec (Word 3) 5 Alg.CoreFunSem (buf, x) with
  | inl blk =>
      if @toZ (WordToZ 6) count + 1 <? ctx8_limit
      then Some (buffer_empty_value (Word 3) 5,
                 (@fromZ (WordToZ 6) (@toZ (WordToZ 6) count + 1),
                  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (h, blk)))
      else None
  | inr buf' => if @toZ (WordToZ 6) count <? ctx8_limit then Some (buf', (count, h)) else None
  end.

Lemma ctx8_add1_full_option (blk : Ty.tySem (Word 9)) (count : Ty.tySem (Word 6)) (h : Ty.tySem (Word 8)) :
  @ctx8_add1_full optalg (blk, (count, h)) =
    match fst (@increment_word_spec Alg.CoreFunSem 6 count) with
    | inl _ => Some (buffer_empty_value (Word 3) 5,
                     (snd (@increment_word_spec Alg.CoreFunSem 6 count),
                      @Simplicity.SHA256.hashBlock Alg.CoreFunSem (h, blk)))
    | inr _ => None
    end.
Proof.
  pose proof (opt_core (fun alg => @increment_word_spec alg 6) (increment_word_spec_parametric 6) count) as HI.
  pose proof (opt_core (@Simplicity.SHA256.hashBlock) (fun a1 a2 R => @Simplicity.SHA256.hashBlock_Parametric a1 a2 R) (h, blk)) as HH.
  pose proof (opt_core (fun alg => @buffer_empty_spec (Word 3) 5 Ty.Unit alg)
    (buffer_empty_spec_parametric (Word 3) 5 Ty.Unit) tt) as HE.
  cbv beta in HI, HH, HE. rewrite buffer_empty_spec_value in HE.
  unfold ctx8_add1_full.
  repeat progress (cbv beta iota; cbn [fst snd];
    rewrite ?opt_unit, ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden, ?HE, ?HI, ?HH).
  destruct (@increment_word_spec Alg.CoreFunSem 6 count) as [[u|u] y]; cbn [fst snd]; reflexivity.
Qed.

Lemma word64_pow : two_power_nat (bitSize (WordToZ 6)) = 18446744073709551616.
Proof. reflexivity. Qed.

Lemma increment64_numeric (count : Ty.tySem (Word 6)) :
  @toZ BitToZ (fst (@increment_word_spec Alg.CoreFunSem 6 count)) * 18446744073709551616 +
    @toZ (WordToZ 6) (snd (@increment_word_spec Alg.CoreFunSem 6 count)) =
  @toZ (WordToZ 6) count + 1.
Proof.
  assert (H : @toZ (PairToZ BitToZ (WordToZ 6)) (@increment_word_spec Alg.CoreFunSem 6 count) =
      @toZ (WordToZ 6) count + 1).
  { rewrite increment_word_spec_fun, Word.fullAdder_correct, Word.zero_correct.
    change (@toZ BitToZ (inr tt)) with 1. lia. }
  destruct (@increment_word_spec Alg.CoreFunSem 6 count) as [c y]. cbn [fst snd].
  rewrite (@toZ_Pair BitToZ (WordToZ 6)), word64_pow in H. exact H.
Qed.

Lemma word64_range (y : Ty.tySem (Word 6)) : 0 <= @toZ (WordToZ 6) y < 18446744073709551616.
Proof.
  rewrite (@ToZ.Theory.toZ_mod (WordToZ 6) y), word64_pow.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma ctx8_add1_snoc_parametric : Alg.Core.Parametric (@ctx8_add1_snoc).
Proof.
  intros alg1 alg2 R. unfold ctx8_add1_snoc.
  repeat first [apply buffer_snoc_spec_parametric
    | apply Alg.comp_Parametric | apply Alg.pair_Parametric | apply Alg.take_Parametric
    | apply Alg.drop_Parametric | apply Alg.iden_Parametric].
Qed.

Lemma ctx8_add1_option c x : @ctx8_add1_spec optalg (c, x) = ctx8_add1_model c x.
Proof.
  destruct c as [buf [count h]].
  unfold ctx8_add1_spec, ctx8_add1_model. rewrite opt_comp.
  rewrite (opt_core (@ctx8_add1_snoc) ctx8_add1_snoc_parametric).
  match goal with |- context[@buffer_snoc_spec ?X ?d ?alg ?p] =>
    set (sn := @buffer_snoc_spec X d alg p) end.
  change (@ctx8_add1_snoc Alg.CoreFunSem (buf, (count, h), x)) with (sn, (count, h)).
  clearbody sn. cbv beta iota. rewrite opt_comp, opt_case. cbn [fst snd].
  destruct sn as [blk|buf'].
  - rewrite ctx8_add1_full_option.
    pose proof (increment64_numeric count) as HN.
    destruct (@increment_word_spec Alg.CoreFunSem 6 count) as [[u|u] y]; destruct u; cbn [fst snd] in HN |- *.
    + change (@toZ BitToZ (inl tt)) with 0 in HN.
      rewrite opt_comp, opt_pair, opt_iden, sha256_count_assertion_option.
      replace (@toZ (WordToZ 6) count + 1) with (@toZ (WordToZ 6) y) by lia.
      rewrite (@ToZ.Theory.from_toZ (WordToZ 6) y). unfold ctx8_limit.
      destruct (@toZ (WordToZ 6) y <? 36028797018963968); reflexivity.
    + change (@toZ BitToZ (inr tt)) with 1 in HN.
      pose proof (word64_range y) as Hy.
      assert (HF : (@toZ (WordToZ 6) count + 1 <? ctx8_limit) = Datatypes.false)
        by (apply Z.ltb_ge; unfold ctx8_limit; lia).
      rewrite HF. reflexivity.
  - rewrite opt_iden. cbv beta iota. rewrite opt_comp, opt_pair, opt_iden, sha256_count_assertion_option.
    unfold ctx8_limit. destruct (@toZ (WordToZ 6) count <? 36028797018963968); reflexivity.
Qed.

Lemma ctx8_add1_full_parametric : Alg.Assertion.Parametric (@ctx8_add1_full).
Proof.
  intros alg1 alg2 [R [HC HA]]. unfold ctx8_add1_full.
  set (RC := Alg.Core.Parametric.Pack HC).
  set (RA := Alg.Assertion.Parametric.Pack (Alg.Assertion.Parametric.Build_class HC HA)).
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply buffer_empty_spec_parametric].
  - apply (Alg.pair_Parametric RC).
    + apply (Alg.drop_Parametric RC). apply (Alg.comp_Parametric RC).
      * apply (Alg.take_Parametric RC). apply increment_word_spec_parametric.
      * apply (Alg.assertl_Parametric RA). apply (Alg.drop_Parametric RC). apply Alg.iden_Parametric.
    + apply (Alg.comp_Parametric RC).
      * apply (Alg.pair_Parametric RC).
        -- apply (Alg.drop_Parametric RC). apply (Alg.drop_Parametric RC). apply Alg.iden_Parametric.
        -- apply (Alg.take_Parametric RC). apply Alg.iden_Parametric.
      * apply Simplicity.SHA256.hashBlock_Parametric.
Qed.

Lemma ctx8_add1_spec_parametric : Alg.Assertion.Parametric (@ctx8_add1_spec).
Proof.
  intros alg1 alg2 R. pose proof (ctx8_add1_full_parametric alg1 alg2 R) as HFull.
  pose proof (sha256_count_assertion_parametric alg1 alg2 R) as HCount.
  destruct R as [R [HC HA]]. unfold ctx8_add1_spec.
  set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC); [apply ctx8_add1_snoc_parametric|].
  apply (Alg.comp_Parametric RC).
  - apply (Alg.case_Parametric RC); [exact HFull|apply Alg.iden_Parametric].
  - apply (Alg.comp_Parametric RC).
    + apply (Alg.pair_Parametric RC); [exact HCount|apply Alg.iden_Parametric].
    + apply (Alg.drop_Parametric RC). apply Alg.iden_Parametric.
Qed.

(** * ctx8Addn
    ctx8Addn SingleV = ctx8Add1
    ctx8Addn (DoubleV v) = let rec = ctx8Addn v in (oh &&& ioh >>> rec) &&& iih >>> rec *)
Fixpoint ctx8_addn_spec (n : nat) {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Vector (Word 3) n)) sha256_ctx8_type :=
  match n with
  | O => @ctx8_add1_spec term
  | S n =>
      @AC.comp _ _ _ (Alg.Assertion.toCore term)
        (@AC.pair _ _ _ (Alg.Assertion.toCore term)
          (@AC.comp _ _ _ (Alg.Assertion.toCore term)
            (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_addn_spec n term))
          (AC.drop (AC.drop AC.iden)))
        (@ctx8_addn_spec n term)
  end.

Lemma ctx8_addn_spec_parametric n : Alg.Assertion.Parametric (@ctx8_addn_spec n).
Proof.
  induction n; [exact ctx8_add1_spec_parametric|].
  intros alg1 alg2 R. pose proof (IHn alg1 alg2 R) as HRec.
  destruct R as [R [HC HA]]. cbn [ctx8_addn_spec].
  set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC); [|exact HRec].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [|exact HRec].
    apply (Alg.pair_Parametric RC).
    + apply (Alg.take_Parametric RC). apply Alg.iden_Parametric.
    + apply (Alg.drop_Parametric RC). apply (Alg.take_Parametric RC). apply Alg.iden_Parametric.
  - apply (Alg.drop_Parametric RC). apply (Alg.drop_Parametric RC). apply Alg.iden_Parametric.
Qed.

Fixpoint ctx8_add_list (c : Ty.tySem sha256_ctx8_type) (l : list (Ty.tySem (Word 3))) :
    option (Ty.tySem sha256_ctx8_type) :=
  match l with
  | [] => Some c
  | x :: l => match ctx8_add1_model c x with Some c' => ctx8_add_list c' l | None => None end
  end.

Lemma ctx8_add_list_app c l1 l2 :
  ctx8_add_list c (l1 ++ l2) =
    match ctx8_add_list c l1 with Some c' => ctx8_add_list c' l2 | None => None end.
Proof.
  revert c. induction l1 as [|x l1 IH]; intros c; [reflexivity|].
  cbn [app ctx8_add_list]. destruct (ctx8_add1_model c x); [apply IH|reflexivity].
Qed.

Lemma ctx8_addn_option n (c : Ty.tySem sha256_ctx8_type) (v : Ty.tySem (Vector (Word 3) n)) :
  @ctx8_addn_spec n optalg (c, v) = ctx8_add_list c (vector_values (Word 3) n v).
Proof.
  revert c. induction n; intros c.
  - cbn [ctx8_addn_spec vector_values ctx8_add_list]. rewrite ctx8_add1_option.
    destruct (ctx8_add1_model c v); reflexivity.
  - destruct v as [v1 v2]. cbn [ctx8_addn_spec vector_values fst snd].
    rewrite ctx8_add_list_app, <- IHn.
    repeat progress (cbv beta iota; cbn [fst snd];
      rewrite ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden).
    destruct (@ctx8_addn_spec n optalg (c, v1)) as [c'|]; [|reflexivity].
    cbv beta iota. apply IHn.
Qed.
