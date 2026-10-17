(** Canonical blindingEntropyHash: absent byte0; present byte1 and64 bytes. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_add_buffer_spec C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_elements_blinding_entropy_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition blinding_entropy_hash_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type blinding_entropy_value_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ core
      (AC.drop (@AC.comp _ _ _ core
        (AC.pair AC.iden (AC.comp AC.unit (@Word.zero 3 core))) (@ctx8_add1_spec term)))
      (@AC.comp _ _ _ core
        (AC.pair
          (AC.drop (@AC.comp _ _ _ core
            (AC.pair AC.iden (AC.comp AC.unit (Alg.scribe byte_one))) (@ctx8_add1_spec term)))
          (AC.take AC.iden))
        (@ctx8_addn_spec 6 term))).

Lemma blinding_entropy_hash_spec_parametric : Alg.Assertion.Parametric (@blinding_entropy_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_add1_spec_parametric _ _ R) as H1.
  pose proof (ctx8_addn_spec_parametric 6 _ _ R) as H6.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold blinding_entropy_hash_spec. cbv zeta.
  solve [repeat first [exact H1 | exact H6 | apply (Word.zero_Parametric RC) |
    apply (Alg.scribe_Parametric RC) | apply (Alg.comp_Parametric RC) |
    apply (Alg.pair_Parametric RC) | apply (Alg.case_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition blinding_entropy_bytes (v : Ty.tySem blinding_entropy_value_type) : list (Ty.tySem Word8) :=
  match v with
  | inl _ => [byte_zero]
  | inr p => byte_one :: vector_values Word8 6 p
  end.

Lemma blinding_entropy_hash_option c v :
  @blinding_entropy_hash_spec optalg (c, v) = ctx8_add_list c (blinding_entropy_bytes v).
Proof.
  assert (HZ : @Word.zero 3 (Alg.Assertion.toCore optalg) tt = Some byte_zero).
  { exact (opt_core (fun alg => @Word.zero 3 alg)
      (fun a1 a2 R => @Word.zero_Parametric 3 a1 a2 R) tt). }
  assert (H1 : @Alg.scribe Ty.Unit Word8 byte_one (Alg.Assertion.toCore optalg) tt = Some byte_one).
  { rewrite (opt_core (fun alg => @Alg.scribe Ty.Unit Word8 byte_one alg)
      (fun a1 a2 R => @Alg.scribe_Parametric a1 a2 R Ty.Unit Word8 byte_one) tt).
    rewrite Alg.scribe_correct. reflexivity. }
  unfold blinding_entropy_hash_spec. cbv zeta. destruct v as [[] | p]; opt_steps.
  - rewrite opt_unit. cbv beta iota. rewrite HZ, ctx8_add1_option.
    cbn [blinding_entropy_bytes ctx8_add_list].
    destruct (ctx8_add1_model c byte_zero); reflexivity.
  - rewrite opt_unit. cbv beta iota. rewrite H1, ctx8_add1_option.
    cbn [blinding_entropy_bytes ctx8_add_list].
    destruct (ctx8_add1_model c byte_one) as [c' | ]; [ | reflexivity].
    opt_steps. apply (ctx8_addn_option 6).
Qed.

Lemma blinding_entropy_bytes_bound v : Z.of_nat (length (blinding_entropy_bytes v)) <= 65.
Proof.
  destruct v as [[] | p]; cbn [blinding_entropy_bytes length];
    [lia | rewrite vector_values_length; cbn; lia].
Qed.
