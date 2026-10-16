(** The existing literal hashLoop/hashWords programs over any option Reader.
    Counter traversal and list-prefix facts are reused from the checked
    development; no fresh primitive signature or cached hash oracle is used. *)
From Coq Require Import ZArith List Lia PeanoNat.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import Simplicity.Alg Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq C.jet_sha256_iv_init.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_hash_loop.
Require Import C.jet_sha_finalize_spec C.jet_sha_hash_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition hash_reader_alg (E : Type) : Alg.Assertion.Algebra :=
  Alg.AssertionSem (ReaderT_CIMonadZero E option_Monad_Zero).

Section Reader.
Variable E : Type.
Local Notation ra := (hash_reader_alg E).
Local Notation rc := (Alg.Assertion.toCore ra).

Lemma hr_comp {A B C : Ty} (s : rc A B) (t : rc B C) a e :
  @AC.comp A B C rc s t a e = match s a e with Some b => t b e | None => None end.
Proof. cbv. destruct (s a e); reflexivity. Qed.
Lemma hr_pair {A B C : Ty} (s : rc A B) (t : rc A C) a e :
  @AC.pair A B C rc s t a e =
    match s a e, t a e with Some b, Some c => Some (b, c) | _, _ => None end.
Proof. cbv. destruct (s a e), (t a e); reflexivity. Qed.
Lemma hr_take {A B C : Ty} (t : rc A C) (p : Ty.tySem (Ty.Prod A B)) e :
  @AC.take A B C rc t p e = t (fst p) e.
Proof. destruct p; reflexivity. Qed.
Lemma hr_drop {A B C : Ty} (t : rc B C) (p : Ty.tySem (Ty.Prod A B)) e :
  @AC.drop A B C rc t p e = t (snd p) e.
Proof. destruct p; reflexivity. Qed.
Lemma hr_iden {A : Ty} (a : Ty.tySem A) e : @AC.iden A rc a e = Some a.
Proof. reflexivity. Qed.
Lemma hr_unit {A : Ty} (a : Ty.tySem A) e : @AC.unit A rc a e = Some tt.
Proof. reflexivity. Qed.
Lemma hr_case {A B C D : Ty} (s : rc (Ty.Prod A C) D)
    (t : rc (Ty.Prod B C) D) (p : Ty.tySem (Ty.Prod (Ty.Sum A B) C)) e :
  @AC.case A B C D rc s t p e =
    match fst p with inl a => s (a, snd p) e | inr b => t (b, snd p) e end.
Proof. destruct p as [[a|b] c]; reflexivity. Qed.
Lemma hr_injl {A B C : Ty} (t : rc A B) a e :
  @AC.injl A B C rc t a e = match t a e with Some b => Some (inl b) | None => None end.
Proof. cbv. destruct (t a e); reflexivity. Qed.
Lemma hr_injr {A B C : Ty} (t : rc A C) a e :
  @AC.injr A B C rc t a e = match t a e with Some b => Some (inr b) | None => None end.
Proof. cbv. destruct (t a e); reflexivity. Qed.
Lemma hr_copair_iden {A : Ty} (p : Ty.tySem (Ty.Sum A A)) e :
  @AC.copair A A A rc (@AC.iden A rc) (@AC.iden A rc) p e =
    Some (match p with inl a => a | inr a => a end).
Proof. destruct p; reflexivity. Qed.

Lemma hr_assert {A B : Ty} (t : forall alg : Alg.Assertion.Algebra, alg A B)
    (Ht : Alg.Assertion.Parametric t) (a : Ty.tySem A) e :
  t ra a e = t optalg a.
Proof.
  pose proof (@Alg.AssertionSem_initial (ReaderT_CIMonadZero E option_Monad_Zero) A B t Ht a) as Hs.
  refine (eq_trans (f_equal (fun f => f e) Hs) _).
  destruct (t optalg a); reflexivity.
Qed.
Lemma hr_core {A B : Ty} (t : forall alg : Alg.Core.Algebra, alg A B)
    (Ht : Alg.Core.Parametric t) (a : Ty.tySem A) e :
  t rc a e = Some (t Alg.CoreFunSem a).
Proof.
  pose proof (@Alg.CoreSem_initial (ReaderT_CIMonad E option_CIMonad) A B t Ht a) as Hs.
  refine (eq_trans (f_equal (fun f => f e) Hs) _). reflexivity.
Qed.

Lemma hash_loop_body_reader_sem k {C W : Ty}
    (array : ra (Ty.Prod C W) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    (cw : Ty.tySem (Ty.Prod C W)) (ctx : Ty.tySem sha256_ctx8_type) e :
  @hash_loop_body k ra C W array (cw, ctx) e =
    match array cw e with
    | None => None
    | Some (inl _) => Some (inl ctx)
    | Some (inr x) =>
        match ctx8_add_list ctx (vector_values (Word 3) k x) with
        | Some c' => Some (inr c') | None => None end
    end.
Proof.
  unfold hash_loop_body. cbv zeta. rewrite hr_comp, hr_pair, hr_take, hr_drop, hr_iden.
  cbn [fst snd]. destruct (array cw e) as [[u | x] | ]; [ | | reflexivity].
  - rewrite hr_case. cbn [fst snd]. rewrite hr_injl, hr_drop, hr_iden. reflexivity.
  - rewrite hr_case. cbn [fst snd]. rewrite hr_injr, hr_comp, hr_pair, hr_drop, hr_take, !hr_iden.
    cbn [fst snd].
    rewrite (hr_assert (fun alg => @ctx8_addn_spec k alg) (ctx8_addn_spec_parametric k)), ctx8_addn_option.
    reflexivity.
Qed.

Theorem hash_loop_reader_sem (k w : nat) (C : Ty)
    (array : ra (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    (c : Ty.tySem C) (ctx0 : Ty.tySem sha256_ctx8_type) (e : E)
    (xs : list (Ty.tySem (Vector (Word 3) k)))
    (Harr : forall i, array (c, i) e =
      Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end))
    cf (Hcf : ctx8_add_list ctx0 (loop_bytes k (firstn (Z.to_nat (wsize w)) xs)) = Some cf) :
  @hash_loop_spec k w ra C array (c, ctx0) e = Some cf.
Proof.
  pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) xs).
  pose proof (loop_items_length k w xs) as HIL. fold items in HIL.
  set (St := fun i => match ctx8_add_list ctx0 (loop_bytes k (firstn (Z.to_nat i) xs)) with
                       Some c' => c' | None => ctx0 end).
  set (body := fun p => @hash_loop_body k ra C (Word w) array p e).
  assert (HStep : forall wd, wz w wd < Z.of_nat (length items) ->
    body ((c, wd), St (0 + wz w wd)) = Some (inr (St (0 + wz w wd + 1)))).
  { intros wd Hlt. pose proof (wz_range w wd) as HR. unfold body.
    rewrite hash_loop_body_reader_sem, Harr.
    destruct (nth_error xs (Z.to_nat (wz w wd))) as [x|] eqn:Hx.
    - rewrite Z.add_0_l. unfold St.
      rewrite (loop_step k w ctx0 xs cf Hcf (wz w wd) x ltac:(fold items; lia) Hx). reflexivity.
    - apply nth_error_None in Hx. lia. }
  assert (HRun : exists r : Ty.tySem (Ty.Sum sha256_ctx8_type sha256_ctx8_type),
    for_while_run w body c ctx0 = Some r /\ match r with inl a => a | inr a => a end = cf).
  { destruct (Z_lt_le_dec (Z.of_nat (length xs)) (wsize w)) as [Hlt|Hge].
    - assert (HI : items = xs) by (unfold items; apply firstn_all2; lia).
      exists (inl cf). split; [|reflexivity].
      apply (@for_while_run_seq_left C sha256_ctx8_type sha256_ctx8_type St w 0 (Z.of_nat (length xs)) cf body c).
      + lia.
      + intros wd Hw. apply HStep. rewrite HI. lia.
      + intros wd Hw. unfold body. rewrite hash_loop_body_reader_sem, Harr.
        assert (HN : nth_error xs (Z.to_nat (wz w wd)) = None) by (apply nth_error_None; lia).
        rewrite HN. do 2 f_equal.
        pose proof (loop_prefix_some k w ctx0 xs cf Hcf (Z.of_nat (length xs)) ltac:(fold items; rewrite HI; lia)) as HP.
        rewrite Nat2Z.id, firstn_all in HP. pose proof Hcf as HC. fold items in HC.
        rewrite HI in HC. unfold St. congruence.
    - exists (inr cf). split; [|reflexivity].
      pose proof (@for_while_run_seq_right C sha256_ctx8_type sha256_ctx8_type St w 0 body c) as HR.
      assert (HS : St (0 + wsize w) = cf).
      { unfold St. rewrite Z.add_0_l, Hcf. reflexivity. }
      rewrite HS in HR. apply HR.
      intros wd. pose proof (wz_range w wd) as HR2. apply HStep. lia. }
  destruct HRun as (r & HRun & Hr).
  unfold hash_loop_spec. cbv zeta. rewrite hr_comp.
  match goal with |- match ?X with _ => _ end = _ => assert (HFW : X = Some r) end.
  { etransitivity; [exact (for_while_program_reader_sem w (hash_loop_body k array) c ctx0 e)|exact HRun]. }
  rewrite HFW, hr_copair_iden. f_equal. exact Hr.
Qed.

Theorem hash_words_reader_sem (k w : nat) (C : Ty)
    (array : ra (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    (c : Ty.tySem C) (e : E) (xs : list (Ty.tySem (Vector (Word 3) k))) :
  (forall i, array (c, i) e =
    Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  @hash_words_spec k w ra C array c e =
    Some (from_hash256 (hash_words_of k (firstn (Z.to_nat (wsize w)) xs))).
Proof.
  intros Harr HB. pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) xs).
  set (c0 := (buffer_empty_value (Word 3) 5,
    (@Word.zero 6 Alg.CoreFunSem tt, @sha256_iv_spec Alg.CoreFunSem tt)) : Ty.tySem sha256_ctx8_type).
  assert (HT : @toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt) +
    (Z.of_nat (length (buffer_list (Word 3) 5 (buffer_empty_value (Word 3) 5))) +
     Z.of_nat (length (loop_bytes k items))) / 64 < ctx8_limit).
  { rewrite buffer_list_empty, loop_bytes_length.
    change (@toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt)) with 0. cbn [length].
    assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
    eapply Z.le_lt_trans; [|exact HB]. rewrite Z.add_0_l, Z.add_0_l.
    apply Z.div_le_mono; [lia|]. rewrite Nat2Z.inj_mul. apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (ctx8_hash_closed_gen (loop_bytes k items) (buffer_empty_value (Word 3) 5)
    (@Word.zero 6 Alg.CoreFunSem tt) (@sha256_iv_spec Alg.CoreFunSem tt) HT) as (cf & Hcf & HFin).
  rewrite buffer_list_empty, iv_spec_regs in HFin.
  change (@toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt)) with 0 in HFin.
  unfold hash_words_spec. cbv zeta.
  rewrite hr_comp, hr_pair, hr_iden, hr_comp, hr_unit.
  rewrite (hr_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric),
    sha256_ctx8_init_spec_value.
  rewrite hr_comp.
  match goal with |- match ?X with _ => _ end = _ =>
    assert (HX : X = Some cf) by exact (hash_loop_reader_sem k w C array c c0 e xs Harr cf Hcf);
    rewrite HX end.
  rewrite (hr_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact HFin.
Qed.
End Reader.
