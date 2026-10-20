(** Literal hash-element loops under any option Reader.  Reuse the checked
    byte-prefix/step and counter traversal lemmas; no C execution is assumed. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_forWhile_seq C.jet_forWhile_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec.
Require Import C.jet_sha_finalize_spec C.jet_sha_hash_words_reader.
Require Import C.jet_sha_hash_loop_gen C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Section Reader.
Variable E : Type.
Variable X : Ty.
Variable add : forall term : Alg.Assertion.Algebra,
  term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type.
Hypothesis add_parametric : Alg.Assertion.Parametric add.
Variable bytes_of : Ty.tySem X -> list (Ty.tySem (Word 3)).
Hypothesis add_option : forall c x, add optalg (c, x) = ctx8_add_list c (bytes_of x).
Local Notation ra := (hash_reader_alg E).

Lemma gen_loop_body_reader_sem {C W : Ty}
    (array : ra (Ty.Prod C W) (Ty.Sum Ty.Unit X))
    (cw : Ty.tySem (Ty.Prod C W)) (ctx : Ty.tySem sha256_ctx8_type) e :
  @gen_loop_body X add ra C W array (cw, ctx) e =
    match array cw e with
    | None => None
    | Some (inl _) => Some (inl ctx)
    | Some (inr x) =>
        match ctx8_add_list ctx (bytes_of x) with
        | Some c' => Some (inr c') | None => None end
    end.
Proof.
  unfold gen_loop_body. cbv zeta. rewrite hr_comp, hr_pair, hr_take, hr_drop, hr_iden.
  cbn [fst snd]. destruct (array cw e) as [[u | x] | ]; [ | | reflexivity].
  - rewrite hr_case. cbn [fst snd]. rewrite hr_injl, hr_drop, hr_iden. reflexivity.
  - rewrite hr_case. cbn [fst snd]. rewrite hr_injr, hr_comp, hr_pair, hr_drop, hr_take, !hr_iden.
    cbn [fst snd]. rewrite (hr_assert E add add_parametric), add_option. reflexivity.
Qed.

Theorem gen_loop_run_reader_sem (w : nat) (C : Ty)
    (array : ra (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit X))
    (c : Ty.tySem C) (ctx0 : Ty.tySem sha256_ctx8_type) (e : E)
    (xs : list (Ty.tySem X))
    (Harr : forall i, array (c, i) e =
      Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end))
    cf (Hcf : ctx8_add_list ctx0 (gen_bytes X bytes_of (firstn (Z.to_nat (wsize w)) xs)) = Some cf) :
  exists r : Ty.tySem (Ty.Sum sha256_ctx8_type sha256_ctx8_type),
    @gen_loop_run X add w ra C array (c, ctx0) e = Some r /\
    match r with inl a => a | inr a => a end = cf.
Proof.
  pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) xs).
  assert (HIL : length items = Nat.min (Z.to_nat (wsize w)) (length xs)) by
    (unfold items; apply firstn_length).
  set (St := fun i => match ctx8_add_list ctx0 (gen_bytes X bytes_of (firstn (Z.to_nat i) xs)) with
                       Some c' => c' | None => ctx0 end).
  set (body := fun p => @gen_loop_body X add ra C (Word w) array p e).
  assert (HStep : forall wd, wz w wd < Z.of_nat (length items) ->
    body ((c, wd), St (0 + wz w wd)) = Some (inr (St (0 + wz w wd + 1)))).
  { intros wd Hlt. pose proof (wz_range w wd) as HR. unfold body.
    refine (eq_trans (gen_loop_body_reader_sem array (c, wd) (St (0 + wz w wd)) e) _).
    rewrite Harr.
    destruct (nth_error xs (Z.to_nat (wz w wd))) as [x|] eqn:Hx.
    - rewrite Z.add_0_l. unfold St.
      rewrite (gen_step X bytes_of w ctx0 xs cf Hcf (wz w wd) x ltac:(fold items; lia) Hx).
      reflexivity.
    - apply nth_error_None in Hx. lia. }
  assert (HRun : exists r : Ty.tySem (Ty.Sum sha256_ctx8_type sha256_ctx8_type),
    for_while_run w body c ctx0 = Some r /\ match r with inl a => a | inr a => a end = cf).
  { destruct (Z_lt_le_dec (Z.of_nat (length xs)) (wsize w)) as [Hlt|Hge].
    - assert (HI : items = xs) by (unfold items; apply firstn_all2; lia).
      exists (inl cf). split; [|reflexivity].
      apply (@for_while_run_seq_left C sha256_ctx8_type sha256_ctx8_type St w 0 (Z.of_nat (length xs)) cf body c).
      + lia.
      + intros wd Hw. apply HStep. rewrite HI. lia.
      + intros wd Hw. unfold body.
        refine (eq_trans (gen_loop_body_reader_sem array (c, wd) (St (Z.of_nat (length xs))) e) _).
        rewrite Harr.
        assert (HN : nth_error xs (Z.to_nat (wz w wd)) = None) by (apply nth_error_None; lia).
        rewrite HN. do 2 f_equal.
        pose proof (gen_prefix_some X bytes_of w ctx0 xs cf Hcf
          (Z.of_nat (length xs)) ltac:(fold items; rewrite HI; lia)) as HP.
        rewrite Nat2Z.id, firstn_all in HP. pose proof Hcf as HC. fold items in HC.
        rewrite HI in HC. unfold St. congruence.
    - exists (inr cf). split; [|reflexivity].
      pose proof (@for_while_run_seq_right C sha256_ctx8_type sha256_ctx8_type St w 0 body c) as HR.
      assert (HS : St (0 + wsize w) = cf).
      { unfold St. rewrite Z.add_0_l, Hcf. reflexivity. }
      rewrite HS in HR. apply HR.
      intros wd. pose proof (wz_range w wd) as HR2. apply HStep. lia. }
  destruct HRun as (r & HRun & Hr). exists r. split; [|exact Hr].
  etransitivity; [exact (for_while_program_reader_sem w (gen_loop_body X add array) c ctx0 e)|exact HRun].
Qed.
End Reader.

Definition hash_elems_spec (X : Ty)
    (add : forall term : Alg.Assertion.Algebra, term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type)
    (w : nat) {term : Alg.Assertion.Algebra}
    (array : term (Ty.Prod Ty.Unit (Word w)) (Ty.Sum Ty.Unit X)) : term Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
    (@AC.comp _ _ _ core (@gen_loop_run X add w term Ty.Unit array)
      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).

Lemma hash_elems_spec_parametric X add (HA : Alg.Assertion.Parametric add) w
    {alg1 alg2 : Alg.Assertion.Algebra} (R : Alg.Assertion.Parametric.Rel alg1 alg2) a1 a2 :
  Alg.Assertion.Parametric.rel R a1 a2 ->
  Alg.Assertion.Parametric.rel R (@hash_elems_spec X add w alg1 a1) (@hash_elems_spec X add w alg2 a2).
Proof.
  intros Harr. pose proof (ctx8_finalize_spec_parametric _ _ R) as HF.
  pose proof (gen_loop_run_parametric X add HA w R a1 a2 Harr) as HL.
  destruct R as [R [HC HAm]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold hash_elems_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply Alg.unit_Parametric|apply (sha256_ctx8_init_spec_parametric _ _ RC)].
  - apply (Alg.comp_Parametric RC); [exact HL|]. apply (Alg.copair_Parametric RC); exact HF.
Qed.

Lemma hr_copair (E : Type) {A B C : Ty}
    (s : hash_reader_alg E A C) (t : hash_reader_alg E B C)
    (x : Ty.tySem (Ty.Sum A B)) e :
  @AC.copair A B C (Alg.Assertion.toCore (hash_reader_alg E)) s t x e =
    match x with inl a => s a e | inr b => t b e end.
Proof. destruct x; reflexivity. Qed.

Theorem hash_elems_reader_sem (E : Type) (X : Ty)
    (add : forall term : Alg.Assertion.Algebra, term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type)
    (HA : Alg.Assertion.Parametric add) (bytes_of : Ty.tySem X -> list (Ty.tySem (Word 3)))
    (Hadd : forall c x, add optalg (c, x) = ctx8_add_list c (bytes_of x)) w
    (array : hash_reader_alg E (Ty.Prod Ty.Unit (Word w)) (Ty.Sum Ty.Unit X))
    (e : E) (xs : list (Ty.tySem X)) N :
  (forall i, array (tt, i) e =
    Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  (forall x, Z.of_nat (length (bytes_of x)) <= N) ->
  0 <= N -> N * wsize w / 64 < ctx8_limit ->
  @hash_elems_spec X add w (hash_reader_alg E) array tt e =
    Some (from_hash256 (elems_hash_of X bytes_of w xs)).
Proof.
  intros Harr Hbytes HN HB. pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) xs).
  destruct (init_hash_sem (gen_bytes X bytes_of items)) as (cf & H1 & H2).
  { eapply Z.le_lt_trans; [|exact HB]. apply Z.div_le_mono; [lia|].
    eapply Z.le_trans; [apply (gen_bytes_length_le X bytes_of N Hbytes)|].
    assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
    apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (gen_loop_run_reader_sem E X add HA bytes_of Hadd w Ty.Unit array tt
    (@sha256_ctx8_init_spec Alg.CoreFunSem tt) e xs Harr cf H1) as (r & Hr1 & Hr2).
  unfold hash_elems_spec. cbv zeta. rewrite hr_comp, hr_pair, hr_unit.
  rewrite (hr_core E (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric), hr_comp.
  match goal with |- match ?Y with _ => _ end = _ =>
    assert (HX : Y = Some r) by exact Hr1; rewrite HX end.
  rewrite hr_copair.
  transitivity (@ctx8_finalize_spec (hash_reader_alg E) cf e).
  { destruct r; cbn in Hr2; subst; reflexivity. }
  rewrite (hr_assert E (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.
