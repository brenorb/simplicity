(** Literal ports of Programs.Bitcoin.mkLibAssert.outpointHash and annexHash
    with their option semantics as byte lists added to the context.
      outpointHash = (oh &&& ioh >>> ctx8Add32) &&& iih >>> ctx8Add4
      annexHash = ih &&& oh
              >>> match (ih &&& take (zero word8) >>> ctx8Add1)
                        ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32) *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_add_buffer_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition outpoint_hash_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type :=
  @AC.comp _ _ _ (Alg.Assertion.toCore term)
    (@AC.pair _ _ _ (Alg.Assertion.toCore term)
      (@AC.comp _ _ _ (Alg.Assertion.toCore term)
        (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_addn_spec 5 term))
      (AC.drop (AC.drop AC.iden)))
    (@ctx8_addn_spec 2 term).

Definition byte_one : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 1.

Definition annex_hash_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type :=
  @AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ (Alg.Assertion.toCore term)
      (@AC.comp _ _ _ (Alg.Assertion.toCore term)
        (AC.pair (AC.drop AC.iden) (AC.take (@Word.zero 3 (Alg.Assertion.toCore term))))
        (@ctx8_add1_spec term))
      (@AC.comp _ _ _ (Alg.Assertion.toCore term)
        (@AC.pair _ _ _ (Alg.Assertion.toCore term)
          (@AC.comp _ _ _ (Alg.Assertion.toCore term)
            (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe byte_one)))
            (@ctx8_add1_spec term))
          (AC.take AC.iden))
        (@ctx8_addn_spec 5 term))).

Lemma outpoint_hash_spec_parametric : Alg.Assertion.Parametric (@outpoint_hash_spec).
Proof.
  intros alg1 alg2 R. pose proof (ctx8_addn_spec_parametric 5 alg1 alg2 R) as H5.
  pose proof (ctx8_addn_spec_parametric 2 alg1 alg2 R) as H2.
  destruct R as [R [HC HA]]. unfold outpoint_hash_spec. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC); [|exact H2].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [|exact H5].
    apply (Alg.pair_Parametric RC); [apply (Alg.take_Parametric RC), Alg.iden_Parametric|].
    apply (Alg.drop_Parametric RC), (Alg.take_Parametric RC), Alg.iden_Parametric.
  - apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
Qed.

Lemma annex_hash_spec_parametric : Alg.Assertion.Parametric (@annex_hash_spec).
Proof.
  intros alg1 alg2 R. pose proof (ctx8_addn_spec_parametric 5 alg1 alg2 R) as H5.
  pose proof (ctx8_add1_spec_parametric alg1 alg2 R) as H1.
  destruct R as [R [HC HA]]. unfold annex_hash_spec. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC)|apply (Alg.take_Parametric RC)];
      apply Alg.iden_Parametric.
  - apply (Alg.case_Parametric RC).
    + apply (Alg.comp_Parametric RC); [|exact H1].
      apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC), Alg.iden_Parametric|].
      apply (Alg.take_Parametric RC). apply (Word.zero_Parametric RC).
    + apply (Alg.comp_Parametric RC); [|exact H5].
      apply (Alg.pair_Parametric RC); [|apply (Alg.take_Parametric RC), Alg.iden_Parametric].
      apply (Alg.comp_Parametric RC); [|exact H1].
      apply (Alg.pair_Parametric RC); [apply (Alg.drop_Parametric RC), Alg.iden_Parametric|].
      apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply (Alg.scribe_Parametric RC)].
Qed.

Lemma outpoint_hash_option (c : Ty.tySem sha256_ctx8_type) (h : Ty.tySem (Word 8)) (i : Ty.tySem (Word 5)) :
  @outpoint_hash_spec optalg (c, (h, i)) =
    ctx8_add_list c (vector_values (Word 3) 5 h ++ vector_values (Word 3) 2 i).
Proof.
  unfold outpoint_hash_spec. opt_steps. rewrite ctx8_add_list_app, (ctx8_addn_option 5).
  destruct (ctx8_add_list c (vector_values (Word 3) 5 h)) as [c'|]; [|reflexivity].
  opt_steps. apply (ctx8_addn_option 2).
Qed.

Definition byte_zero : Ty.tySem (Word 3) := @Word.zero 3 Alg.CoreFunSem tt.

Lemma annex_hash_option (c : Ty.tySem sha256_ctx8_type) (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) :
  @annex_hash_spec optalg (c, a) =
    ctx8_add_list c (match a with
                     | inl _ => [byte_zero]
                     | inr h => byte_one :: vector_values (Word 3) 5 h
                     end).
Proof.
  assert (HZ : forall u, @Word.zero 3 (Alg.Assertion.toCore optalg) u = Some (@Word.zero 3 Alg.CoreFunSem u))
    by (intro u; exact (opt_core (fun alg => @Word.zero 3 alg) (fun a1 a2 R => @Word.zero_Parametric 3 a1 a2 R) u)).
  assert (HS : forall u, @Alg.scribe Ty.Unit (Word 3) byte_one (Alg.Assertion.toCore optalg) u = Some byte_one).
  { intro u. rewrite (opt_core (fun alg => @Alg.scribe Ty.Unit (Word 3) byte_one alg)
      (fun a1 a2 R => @Alg.scribe_Parametric a1 a2 R Ty.Unit (Word 3) byte_one) u).
    rewrite Alg.scribe_correct. reflexivity. }
  unfold annex_hash_spec. destruct a as [u|h]; opt_steps.
  - rewrite HZ. cbv beta iota. destruct u. rewrite ctx8_add1_option. cbn [ctx8_add_list].
    fold byte_zero. destruct (ctx8_add1_model c byte_zero); reflexivity.
  - rewrite opt_unit. cbv beta iota. rewrite HS. cbv beta iota. rewrite ctx8_add1_option.
    cbn [ctx8_add_list]. destruct (ctx8_add1_model c byte_one) as [c'|]; [|reflexivity].
    opt_steps. apply (ctx8_addn_option 5).
Qed.
