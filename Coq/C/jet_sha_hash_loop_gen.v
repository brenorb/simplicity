(** The loop shared by hashLoop and the outpoint and annex hashes of
    Bitcoin.Programs.SigHash:
      body = take array &&& ih >>> match (injl ih) (injr (ih &&& oh >>> add))
      forWhile w body
    generic in the element type and in the program [add] that absorbs one
    element, and its value.  No C execution here. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq.
Require Import C.jet_sha_ctx8_spec C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Lemma fx_copair {A B D : Ty} (s : @Alg.Core.domain fullcore A D) (t : @Alg.Core.domain fullcore B D)
    (x : Ty.tySem (Ty.Sum A B)) e :
  @AC.copair A B D fullcore s t x e = match x with inl a => s a e | inr b => t b e end.
Proof. destruct x; reflexivity. Qed.

Section GenLoop.
Variable X : Ty.
Variable add : forall term : Alg.Assertion.Algebra,
  @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type X) sha256_ctx8_type.
Hypothesis add_parametric : Alg.Assertion.Parametric add.
Variable bytes_of : Ty.tySem X -> list (Ty.tySem (Word 3)).
Hypothesis add_option : forall c x, add optalg (c, x) = ctx8_add_list c (bytes_of x).

Definition gen_loop_body {term : Alg.Assertion.Algebra} {C W : Ty}
    (array : @Alg.Assertion.domain term (Ty.Prod C W) (Ty.Sum Ty.Unit X)) :
    @Alg.Assertion.domain term (Ty.Prod (Ty.Prod C W) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.take _ _ _ core array) (@AC.drop _ _ _ core (@AC.iden _ core)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)))
      (@AC.injr _ _ _ core (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)) (@AC.take _ _ _ core (@AC.iden _ core)))
        (add term)))).

Definition gen_loop_run (w : nat) {term : Alg.Assertion.Algebra} {C : Ty}
    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit X)) :
    @Alg.Assertion.domain term (Ty.Prod C sha256_ctx8_type) (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  @for_while_program w _ _ _ (Alg.Assertion.toCore term) (gen_loop_body array).

Lemma gen_loop_run_parametric w {C : Ty} {alg1 alg2 : Alg.Assertion.Algebra}
    (R : Alg.Assertion.Parametric.Rel alg1 alg2) a1 a2 :
  Alg.Assertion.Parametric.rel R a1 a2 ->
  Alg.Assertion.Parametric.rel R (@gen_loop_run w alg1 C a1) (@gen_loop_run w alg2 C a2).
Proof.
  intros HA. pose proof (add_parametric _ _ R) as Hk.
  destruct R as [R [HC HAm]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold gen_loop_run, gen_loop_body. cbv zeta.
  apply (for_while_program_parametric w RC).
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply (Alg.take_Parametric RC); exact HA|].
    apply (Alg.drop_Parametric RC), Alg.iden_Parametric.
  - apply (Alg.case_Parametric RC).
    + apply (Alg.injl_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
    + apply (Alg.injr_Parametric RC), (Alg.comp_Parametric RC); [|exact Hk].
      apply (Alg.pair_Parametric RC);
        [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)]; apply Alg.iden_Parametric.
Qed.

Lemma gen_loop_body_sem {C W : Ty}
    (array : @Alg.Assertion.domain fullassert (Ty.Prod C W) (Ty.Sum Ty.Unit X))
    (cw : Ty.tySem (Ty.Prod C W)) (ctx : Ty.tySem sha256_ctx8_type) e :
  @gen_loop_body fullassert C W array (cw, ctx) e =
    match array cw e with
    | None => None
    | Some (inl _) => Some (inl ctx)
    | Some (inr x) =>
        match ctx8_add_list ctx (bytes_of x) with
        | Some c' => Some (inr c')
        | None => None
        end
    end.
Proof.
  unfold gen_loop_body. cbv zeta. rewrite fx_comp, fx_pair, fx_take, fx_drop, fx_iden. cbn [fst snd].
  destruct (array cw e) as [[u|x]|]; [| |reflexivity].
  - rewrite fx_case. cbn [fst snd]. rewrite fx_injl, fx_drop, fx_iden. reflexivity.
  - rewrite fx_case. cbn [fst snd]. rewrite fx_injr, fx_comp, fx_pair, fx_drop, fx_take, !fx_iden.
    cbn [fst snd]. rewrite (fx_assert add add_parametric), add_option. reflexivity.
Qed.

Definition gen_bytes (l : list (Ty.tySem X)) : list (Ty.tySem (Word 3)) := concat (map bytes_of l).

Lemma gen_bytes_app l1 l2 : gen_bytes (l1 ++ l2) = gen_bytes l1 ++ gen_bytes l2.
Proof. unfold gen_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Section Run.
Variables (w : nat) (C : Ty).
Variable array : @Alg.Assertion.domain fullassert (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit X).
Variables (c : Ty.tySem C) (ctx0 : Ty.tySem sha256_ctx8_type) (e : ext_environment).
Variable xs : list (Ty.tySem X).
Hypothesis Harr : forall i, array (c, i) e =
  Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end).
Variable cf : Ty.tySem sha256_ctx8_type.
Hypothesis Hcf : ctx8_add_list ctx0 (gen_bytes (firstn (Z.to_nat (wsize w)) xs)) = Some cf.

Let items := firstn (Z.to_nat (wsize w)) xs.
Let St (i : Z) : Ty.tySem sha256_ctx8_type :=
  match ctx8_add_list ctx0 (gen_bytes (firstn (Z.to_nat i) xs)) with Some c' => c' | None => ctx0 end.

Lemma gen_prefix_some i : 0 <= i <= Z.of_nat (length items) ->
  ctx8_add_list ctx0 (gen_bytes (firstn (Z.to_nat i) xs)) = Some (St i).
Proof.
  intros Hi. pose proof (wsize_pos w) as HW.
  assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
  assert (HE : firstn (Z.to_nat i) xs = firstn (Z.to_nat i) items).
  { unfold items. rewrite firstn_firstn. f_equal. lia. }
  pose proof Hcf as H. fold items in H.
  rewrite <- (firstn_skipn (Z.to_nat i) items), gen_bytes_app, ctx8_add_list_app, <- HE in H.
  unfold St. destruct (ctx8_add_list ctx0 (gen_bytes (firstn (Z.to_nat i) xs))); [reflexivity|discriminate].
Qed.

Lemma gen_step i x : 0 <= i < Z.of_nat (length items) -> nth_error xs (Z.to_nat i) = Some x ->
  ctx8_add_list (St i) (bytes_of x) = Some (St (i + 1)).
Proof.
  intros Hi Hx. pose proof (gen_prefix_some (i + 1) ltac:(lia)) as H1.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in H1 by lia.
  rewrite (firstn_snoc xs (Z.to_nat i) x Hx), gen_bytes_app, ctx8_add_list_app in H1.
  rewrite (gen_prefix_some i ltac:(lia)) in H1.
  unfold gen_bytes in H1 at 1. cbn [map concat] in H1. rewrite app_nil_r in H1. exact H1.
Qed.

Theorem gen_loop_run_sem :
  exists r : Ty.tySem (Ty.Sum sha256_ctx8_type sha256_ctx8_type),
    @gen_loop_run w fullassert C array (c, ctx0) e = Some r /\
    match r with inl a => a | inr a => a end = cf.
Proof.
  pose proof (wsize_pos w) as HW.
  assert (HIL : length items = Nat.min (Z.to_nat (wsize w)) (length xs)) by (unfold items; apply firstn_length).
  set (body := fun p => @gen_loop_body fullassert C (Word w) array p e).
  assert (HStep : forall wd, wz w wd < Z.of_nat (length items) ->
    body ((c, wd), St (0 + wz w wd)) = Some (inr (St (0 + wz w wd + 1)))).
  { intros wd Hlt. pose proof (wz_range w wd) as HR. unfold body.
    refine (eq_trans (gen_loop_body_sem array (c, wd) (St (0 + wz w wd)) e) _). rewrite Harr.
    destruct (nth_error xs (Z.to_nat (wz w wd))) as [x|] eqn:Hx.
    - rewrite Z.add_0_l. rewrite (gen_step (wz w wd) x ltac:(lia) Hx). reflexivity.
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
        refine (eq_trans (gen_loop_body_sem array (c, wd) (St (Z.of_nat (length xs))) e) _). rewrite Harr.
        assert (HN : nth_error xs (Z.to_nat (wz w wd)) = None) by (apply nth_error_None; lia).
        rewrite HN. do 2 f_equal.
        pose proof (gen_prefix_some (Z.of_nat (length xs)) ltac:(rewrite HI; lia)) as HP.
        rewrite Nat2Z.id, firstn_all in HP. pose proof Hcf as Hcf'. fold items in Hcf'.
        rewrite HI in Hcf'. congruence.
    - exists (inr cf). split; [|reflexivity].
      pose proof (@for_while_run_seq_right C sha256_ctx8_type sha256_ctx8_type St w 0 body c) as HR.
      assert (HS : St (0 + wsize w) = cf).
      { unfold St. rewrite Z.add_0_l. rewrite Hcf. reflexivity. }
      rewrite HS in HR. apply HR.
      intros wd. pose proof (wz_range w wd) as HR2. apply HStep. lia. }
  destruct HRun as (r & HRun & Hr). exists r. split; [|exact Hr].
  etransitivity; [exact (for_while_program_reader_sem w (gen_loop_body array) c ctx0 e)|exact HRun].
Qed.

End Run.
End GenLoop.
