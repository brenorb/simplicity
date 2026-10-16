(** Shared literal (ctx, (byte, bytes)) absorber.  This is the exact
    ctx8Add1 followed by ctx8Addn routing used by confidential serializers. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_add_buffer_spec.
Import ListNotations.
Set Default Timeout 10.

Definition ctx8_tagged_word_spec (k : nat) {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (Ty.Prod Word8 (Vector Word8 k))) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_add1_spec term))
      (AC.drop (AC.drop AC.iden)))
    (@ctx8_addn_spec k term).

Lemma ctx8_tagged_word_spec_parametric k :
  Alg.Assertion.Parametric (@ctx8_tagged_word_spec k).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_add1_spec_parametric _ _ R) as H1.
  pose proof (ctx8_addn_spec_parametric k _ _ R) as HN.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold ctx8_tagged_word_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|exact HN].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [|exact H1].
    apply (Alg.pair_Parametric RC).
    + apply (Alg.take_Parametric RC), Alg.iden_Parametric.
    + apply (Alg.drop_Parametric RC), (Alg.take_Parametric RC), Alg.iden_Parametric.
  - apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
Qed.

Lemma ctx8_tagged_word_option k (c : Ty.tySem sha256_ctx8_type)
    (tag : Ty.tySem Word8) (v : Ty.tySem (Vector Word8 k)) :
  @ctx8_tagged_word_spec k optalg (c, (tag, v)) =
    ctx8_add_list c (tag :: vector_values Word8 k v).
Proof.
  unfold ctx8_tagged_word_spec. cbv zeta. opt_steps.
  rewrite ctx8_add1_option. cbn [ctx8_add_list].
  destruct (ctx8_add1_model c tag) as [c'|]; [|reflexivity].
  opt_steps. apply (ctx8_addn_option k).
Qed.
