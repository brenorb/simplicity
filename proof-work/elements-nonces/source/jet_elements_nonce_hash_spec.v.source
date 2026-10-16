(** Literal Elements nonceHash.  Native Word256 payloads are not field
    elements.  None contributes byte0; a present nonce contributes its
    prefix1/2/3 and all32 payload bytes. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_add_buffer_spec C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_sha_tagged_word_spec.
Import ListNotations.
Set Default Timeout 10.

Definition elements_nonce_conf_type : Ty := Ty.Sum (Ty.Prod Bit Word256) Word256.
Definition elements_nonce_type : Ty := Ty.Sum Ty.Unit elements_nonce_conf_type.
Definition nonce_byte_two : Ty.tySem Word8 := @fromZ (WordToZ 3) 2.
Definition nonce_byte_three : Ty.tySem Word8 := @fromZ (WordToZ 3) 3.

Definition elements_nonce_tag_payload_spec {term : Alg.Core.Algebra} :
    term elements_nonce_conf_type (Ty.Prod Word8 Word256) :=
  AC.copair
    (AC.pair (AC.take (AC.copair (Alg.scribe nonce_byte_two) (Alg.scribe nonce_byte_three)))
      (AC.drop AC.iden))
    (AC.pair (AC.comp AC.unit (Alg.scribe byte_one)) AC.iden).

Lemma elements_nonce_tag_payload_spec_parametric :
  Alg.Core.Parametric (@elements_nonce_tag_payload_spec).
Proof.
  intros alg1 alg2 R. unfold elements_nonce_tag_payload_spec.
  solve [repeat first [apply Alg.scribe_Parametric | apply Alg.copair_Parametric | apply Alg.pair_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.comp_Parametric |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_nonce_hash_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type elements_nonce_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ core
      (@AC.comp _ _ _ core
        (AC.pair (AC.drop AC.iden) (AC.take (@Word.zero 3 core))) (@ctx8_add1_spec term))
      (@AC.comp _ _ _ core
        (AC.pair (AC.drop AC.iden) (AC.take (@elements_nonce_tag_payload_spec core)))
        (@ctx8_tagged_word_spec 5 term))).

Lemma elements_nonce_hash_spec_parametric :
  Alg.Assertion.Parametric (@elements_nonce_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_add1_spec_parametric _ _ R) as H1.
  pose proof (ctx8_tagged_word_spec_parametric 5 _ _ R) as HT.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  pose proof (elements_nonce_tag_payload_spec_parametric _ _ RC) as HP.
  unfold elements_nonce_hash_spec. cbv zeta.
  solve [repeat first [exact H1 | exact HT | exact HP | apply (Word.zero_Parametric RC) |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.take_Parametric RC) |
    apply (Alg.drop_Parametric RC) |
    apply Alg.iden_Parametric]].
Qed.

Definition elements_nonce_bytes (v : Ty.tySem elements_nonce_type) : list (Ty.tySem Word8) :=
  match v with
  | inl _ => [byte_zero]
  | inr (inl (odd, h)) =>
      (match odd with inl _ => nonce_byte_two | inr _ => nonce_byte_three end) ::
        vector_values Word8 5 h
  | inr (inr h) => byte_one :: vector_values Word8 5 h
  end.

Lemma elements_nonce_tag_payload_value (v : Ty.tySem elements_nonce_conf_type) :
  @elements_nonce_tag_payload_spec Alg.CoreFunSem v =
  match v with
  | inl (odd, h) =>
      (match odd with inl _ => nonce_byte_two | inr _ => nonce_byte_three end, h)
  | inr h => (byte_one, h)
  end.
Proof.
  destruct v as [p | payload];
    [destruct p as [parity payload]; destruct parity as [z | z] | ];
    unfold elements_nonce_tag_payload_spec; reflexivity.
Qed.

Lemma elements_nonce_hash_option (c : Ty.tySem sha256_ctx8_type)
    (v : Ty.tySem elements_nonce_type) :
  @elements_nonce_hash_spec optalg (c, v) = ctx8_add_list c (elements_nonce_bytes v).
Proof.
  assert (HZ : forall u, @Word.zero 3 (Alg.Assertion.toCore optalg) u = Some byte_zero).
  { intros []. exact (opt_core (fun alg => @Word.zero 3 alg)
      (fun a1 a2 R => @Word.zero_Parametric 3 a1 a2 R) tt). }
  assert (HP : forall x,
    @elements_nonce_tag_payload_spec (Alg.Assertion.toCore optalg) x =
    Some (@elements_nonce_tag_payload_spec Alg.CoreFunSem x)).
  { intro x. exact (opt_core (@elements_nonce_tag_payload_spec)
      elements_nonce_tag_payload_spec_parametric x). }
  unfold elements_nonce_hash_spec. cbv zeta.
  destruct v as [[] | x]; opt_steps.
  - rewrite HZ. cbv beta iota. rewrite ctx8_add1_option.
    cbn [elements_nonce_bytes ctx8_add_list].
    destruct (ctx8_add1_model c byte_zero); reflexivity.
  - rewrite HP, elements_nonce_tag_payload_value.
    destruct x as [p | payload];
      [destruct p as [parity payload]; destruct parity as [z | z] | ]; cbv beta iota; opt_steps;
      apply (ctx8_tagged_word_option 5).
Qed.

Lemma elements_nonce_bytes_bound (v : Ty.tySem elements_nonce_type) :
  (length (elements_nonce_bytes v) <= 33)%nat.
Proof.
  destruct v as [[] | [[odd h] | h]]; cbn [elements_nonce_bytes length];
    try rewrite vector_values_length; cbn; lia.
Qed.
