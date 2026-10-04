(** Literal port of Programs.Sha256.hashLoop
      hashLoop v = \w array ->
        let body = take array &&& ih
               >>> match (injl ih) (injr (ih &&& oh >>> ctx8Addv))
        in forWhile w body >>> copair iden iden
    and its value over the united Bitcoin signature: the context that has
    absorbed the array's elements in order.  No C execution here. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq.
Require Import C.jet_sha_ctx8_spec C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Definition hash_loop_body (k : nat) {term : Alg.Assertion.Algebra} {C W : Ty}
    (array : @Alg.Assertion.domain term (Ty.Prod C W) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :
    @Alg.Assertion.domain term (Ty.Prod (Ty.Prod C W) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.take _ _ _ core array) (@AC.drop _ _ _ core (@AC.iden _ core)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)))
      (@AC.injr _ _ _ core (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@AC.drop _ _ _ core (@AC.iden _ core)) (@AC.take _ _ _ core (@AC.iden _ core)))
        (@ctx8_addn_spec k term)))).

Definition hash_loop_spec (k w : nat) {term : Alg.Assertion.Algebra} {C : Ty}
    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :
    @Alg.Assertion.domain term (Ty.Prod C sha256_ctx8_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (@for_while_program w _ _ _ core (hash_loop_body k array))
    (@AC.copair _ _ _ core (@AC.iden _ core) (@AC.iden _ core)).

Lemma hash_loop_spec_parametric k w {C : Ty} {alg1 alg2 : Alg.Assertion.Algebra}
    (R : Alg.Assertion.Parametric.Rel alg1 alg2) a1 a2 :
  Alg.Assertion.Parametric.rel R a1 a2 ->
  Alg.Assertion.Parametric.rel R (@hash_loop_spec k w alg1 C a1) (@hash_loop_spec k w alg2 C a2).
Proof.
  intros HA. pose proof (ctx8_addn_spec_parametric k _ _ R) as Hk.
  destruct R as [R [HC HAm]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold hash_loop_spec, hash_loop_body. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (for_while_program_parametric w RC).
    apply (Alg.comp_Parametric RC).
    + apply (Alg.pair_Parametric RC); [apply (Alg.take_Parametric RC); exact HA|].
      apply (Alg.drop_Parametric RC), Alg.iden_Parametric.
    + apply (Alg.case_Parametric RC).
      * apply (Alg.injl_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
      * apply (Alg.injr_Parametric RC), (Alg.comp_Parametric RC); [|exact Hk].
        apply (Alg.pair_Parametric RC);
          [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)]; apply Alg.iden_Parametric.
  - apply (Alg.copair_Parametric RC); apply Alg.iden_Parametric.
Qed.

(** ** Evaluation *)
Lemma fx_take {A B C : Ty} (t : @Alg.Core.domain fullcore A C) (p : Ty.tySem (Ty.Prod A B)) e :
  @AC.take A B C fullcore t p e = t (fst p) e.
Proof. destruct p; reflexivity. Qed.
Lemma fx_drop {A B C : Ty} (t : @Alg.Core.domain fullcore B C) (p : Ty.tySem (Ty.Prod A B)) e :
  @AC.drop A B C fullcore t p e = t (snd p) e.
Proof. destruct p; reflexivity. Qed.
Lemma fx_iden {A : Ty} (a : Ty.tySem A) e : @AC.iden A fullcore a e = Some a.
Proof. reflexivity. Qed.
Lemma fx_case {A B C D : Ty} (s : @Alg.Core.domain fullcore (Ty.Prod A C) D)
    (t : @Alg.Core.domain fullcore (Ty.Prod B C) D) (p : Ty.tySem (Ty.Prod (Ty.Sum A B) C)) e :
  @AC.case A B C D fullcore s t p e =
    match fst p with inl a => s (a, snd p) e | inr b => t (b, snd p) e end.
Proof. destruct p as [[a|b] c]; reflexivity. Qed.
Lemma fx_injl {A B C : Ty} (t : @Alg.Core.domain fullcore A B) a e :
  @AC.injl A B C fullcore t a e = match t a e with Some b => Some (inl b) | None => None end.
Proof. cbv. destruct (t a e); reflexivity. Qed.
Lemma fx_injr {A B C : Ty} (t : @Alg.Core.domain fullcore A C) a e :
  @AC.injr A B C fullcore t a e = match t a e with Some b => Some (inr b) | None => None end.
Proof. cbv. destruct (t a e); reflexivity. Qed.
Lemma fx_copair_iden {A : Ty} (x : Ty.tySem (Ty.Sum A A)) e :
  @AC.copair A A A fullcore (@AC.iden A fullcore) (@AC.iden A fullcore) x e =
    Some (match x with inl a => a | inr a => a end).
Proof. destruct x; reflexivity. Qed.

Lemma hash_loop_body_sem k {C W : Ty}
    (array : @Alg.Assertion.domain fullassert (Ty.Prod C W) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    (cw : Ty.tySem (Ty.Prod C W)) (ctx : Ty.tySem sha256_ctx8_type) e :
  @hash_loop_body k fullassert C W array (cw, ctx) e =
    match array cw e with
    | None => None
    | Some (inl _) => Some (inl ctx)
    | Some (inr x) =>
        match ctx8_add_list ctx (vector_values (Word 3) k x) with
        | Some c' => Some (inr c')
        | None => None
        end
    end.
Proof.
  unfold hash_loop_body. cbv zeta. rewrite fx_comp, fx_pair, fx_take, fx_drop, fx_iden. cbn [fst snd].
  destruct (array cw e) as [[u|x]|]; [| |reflexivity].
  - rewrite fx_case. cbn [fst snd]. rewrite fx_injl, fx_drop, fx_iden. reflexivity.
  - rewrite fx_case. cbn [fst snd]. rewrite fx_injr, fx_comp, fx_pair, fx_drop, fx_take, !fx_iden.
    cbn [fst snd].
    rewrite (fx_assert (fun alg => @ctx8_addn_spec k alg) (ctx8_addn_spec_parametric k)), ctx8_addn_option.
    reflexivity.
Qed.

Lemma firstn_snoc {A} (l : list A) : forall n x, nth_error l n = Some x ->
  firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|a l IH]; intros [|n] x H; try discriminate.
  - injection H as ->. reflexivity.
  - change (a :: firstn (S n) l = a :: (firstn n l ++ [x])). f_equal. exact (IH n x H).
Qed.

Section Loop.
Variables (k w : nat) (C : Ty).
Variable array : @Alg.Assertion.domain fullassert (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k)).
Variables (c : Ty.tySem C) (ctx0 : Ty.tySem sha256_ctx8_type) (e : ext_environment).
Variable xs : list (Ty.tySem (Vector (Word 3) k)).
Hypothesis Harr : forall i, array (c, i) e =
  Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end).

Definition loop_bytes (l : list (Ty.tySem (Vector (Word 3) k))) : list (Ty.tySem (Word 3)) :=
  concat (map (vector_values (Word 3) k) l).

Variable cf : Ty.tySem sha256_ctx8_type.
Hypothesis Hcf : ctx8_add_list ctx0 (loop_bytes (firstn (Z.to_nat (wsize w)) xs)) = Some cf.

Let items := firstn (Z.to_nat (wsize w)) xs.
Let St (i : Z) : Ty.tySem sha256_ctx8_type :=
  match ctx8_add_list ctx0 (loop_bytes (firstn (Z.to_nat i) xs)) with Some c' => c' | None => ctx0 end.

Lemma loop_bytes_app l1 l2 : loop_bytes (l1 ++ l2) = loop_bytes l1 ++ loop_bytes l2.
Proof. unfold loop_bytes. rewrite map_app, concat_app. reflexivity. Qed.

Lemma loop_prefix_some i : 0 <= i <= Z.of_nat (length items) ->
  ctx8_add_list ctx0 (loop_bytes (firstn (Z.to_nat i) xs)) = Some (St i).
Proof.
  intros Hi. pose proof (wsize_pos w) as HW.
  assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
  assert (HE : firstn (Z.to_nat i) xs = firstn (Z.to_nat i) items).
  { unfold items. rewrite firstn_firstn. f_equal. lia. }
  pose proof Hcf as H. fold items in H.
  rewrite <- (firstn_skipn (Z.to_nat i) items), loop_bytes_app, ctx8_add_list_app, <- HE in H.
  unfold St. destruct (ctx8_add_list ctx0 (loop_bytes (firstn (Z.to_nat i) xs))); [reflexivity|discriminate].
Qed.

Lemma loop_step i x : 0 <= i < Z.of_nat (length items) -> nth_error xs (Z.to_nat i) = Some x ->
  ctx8_add_list (St i) (vector_values (Word 3) k x) = Some (St (i + 1)).
Proof.
  intros Hi Hx. pose proof (loop_prefix_some (i + 1) ltac:(lia)) as H1.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in H1 by lia.
  rewrite (firstn_snoc xs (Z.to_nat i) x Hx), loop_bytes_app, ctx8_add_list_app in H1.
  rewrite (loop_prefix_some i ltac:(lia)) in H1.
  unfold loop_bytes in H1 at 1. cbn [map concat] in H1. rewrite app_nil_r in H1. exact H1.
Qed.

Lemma loop_items_length : length items = Nat.min (Z.to_nat (wsize w)) (length xs).
Proof. unfold items. apply firstn_length. Qed.

Theorem hash_loop_sem : @hash_loop_spec k w fullassert C array (c, ctx0) e = Some cf.
Proof.
  pose proof (wsize_pos w) as HW. pose proof loop_items_length as HIL.
  set (body := fun p => @hash_loop_body k fullassert C (Word w) array p e).
  assert (HStep : forall wd, wz w wd < Z.of_nat (length items) ->
    body ((c, wd), St (0 + wz w wd)) = Some (inr (St (0 + wz w wd + 1)))).
  { intros wd Hlt. pose proof (wz_range w wd) as HR. unfold body.
    rewrite hash_loop_body_sem, Harr.
    destruct (nth_error xs (Z.to_nat (wz w wd))) as [x|] eqn:Hx.
    - rewrite Z.add_0_l. rewrite (loop_step (wz w wd) x ltac:(lia) Hx). reflexivity.
    - apply nth_error_None in Hx. lia. }
  assert (HRun : exists r : Ty.tySem (Ty.Sum sha256_ctx8_type sha256_ctx8_type),
    for_while_run w body c ctx0 = Some r /\ match r with inl a => a | inr a => a end = cf).
  { destruct (Z_lt_le_dec (Z.of_nat (length xs)) (wsize w)) as [Hlt|Hge].
    - assert (HI : items = xs) by (unfold items; apply firstn_all2; lia).
      exists (inl cf). split; [|reflexivity].
      apply (@for_while_run_seq_left C sha256_ctx8_type sha256_ctx8_type St w 0 (Z.of_nat (length xs)) cf body c).
      + lia.
      + intros wd Hw. apply HStep. rewrite HI. lia.
      + intros wd Hw. unfold body. rewrite hash_loop_body_sem, Harr.
        assert (HN : nth_error xs (Z.to_nat (wz w wd)) = None) by (apply nth_error_None; lia).
        rewrite HN. do 2 f_equal.
        pose proof (loop_prefix_some (Z.of_nat (length xs)) ltac:(rewrite HI; lia)) as HP.
        rewrite Nat2Z.id, firstn_all in HP. pose proof Hcf as Hcf'. fold items in Hcf'.
        rewrite HI in Hcf'. congruence.
    - exists (inr cf). split; [|reflexivity].
      pose proof (@for_while_run_seq_right C sha256_ctx8_type sha256_ctx8_type St w 0 body c) as HR.
      assert (HS : St (0 + wsize w) = cf).
      { unfold St. rewrite Z.add_0_l. rewrite Hcf. reflexivity. }
      rewrite HS in HR. apply HR.
      intros wd. pose proof (wz_range w wd) as HR2. apply HStep. lia. }
  destruct HRun as (r & HRun & Hr).
  unfold hash_loop_spec. cbv zeta. rewrite fx_comp.
  match goal with |- match ?X with _ => _ end = _ => assert (HFW : X = Some r) end.
  { etransitivity; [exact (for_while_program_reader_sem w (hash_loop_body k array) c ctx0 e)|exact HRun]. }
  rewrite HFW, fx_copair_iden. f_equal. exact Hr.
Qed.

End Loop.
