(** Canonical indexed issuanceHash program. Reuses the accepted issuance
    calculations, optional asset/amount serializer and literal one8 blinding
    serializer. This semantic bridge alone is not a C equivalence theorem. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_words_hash_program.
Require Import C.jet_elements_input_hash_jets.
Require Import C.jet_forWhile_seq.
Require Import C.jet_elements_issuance_entropy_spec C.jet_elements_issuance_amount_hash_spec.
Require Import C.jet_elements_issuance_amounts_hash_program.
Require Import C.jet_elements_blinding_entropy_spec C.jet_elements_blinding_entropy_hash_spec.
Require Import C.jet_elements_blinding_entropy_canonical.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec.
Require Import C.jet_buffer_input C.jet_buffer_empty_spec C.jet_sha_add_buffer_spec.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_composite_hash C.jet_sha_hash_words_reader.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition elements_single_issuance_tail_type : Ty :=
  Ty.Prod (Ty.Sum Ty.Unit issuance_asset_amount_value_type)
    (Ty.Prod (Ty.Prod (Ty.Sum Ty.Unit Word256) (Ty.Sum Ty.Unit Word256))
      (Ty.Sum Ty.Unit blinding_entropy_value_type)).

Definition elements_single_issuance_payload_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod issuance_asset_amount_value_type elements_single_issuance_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp
                (AC.pair
                  (AC.comp
                    (AC.pair (AC.comp AC.unit (@sha256_ctx8_init_spec core)) (AC.take AC.iden))
                    (@issuance_asset_amount_absorb_spec term))
                  (AC.drop (AC.take (@assert_iden_spec issuance_asset_amount_value_type term))))
                (@issuance_asset_amount_absorb_spec term))
              (AC.drop (AC.drop (AC.take (AC.take (@assert_iden_spec Word256 term))))))
            (@ctx8_addn_spec 5 term))
          (AC.drop (AC.drop (AC.take (AC.drop (@assert_iden_spec Word256 term))))))
        (@ctx8_addn_spec 5 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec blinding_entropy_value_type term)))))
    (AC.comp (@literal_blinding_entropy_hash_spec term) (@ctx8_finalize_spec term)).

Lemma elements_single_issuance_payload_parametric :
  Alg.Assertion.Parametric (@elements_single_issuance_payload_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (issuance_asset_amount_absorb_spec_parametric _ _ R) as HAA.
  pose proof (literal_blinding_entropy_hash_spec_parametric _ _ R) as HB.
  pose proof (ctx8_addn_spec_parametric 5 _ _ R) as H32.
  pose proof (ctx8_finalize_spec_parametric _ _ R) as HF.
  pose proof (assert_iden_spec_parametric issuance_asset_amount_value_type _ _ R) as HAT.
  pose proof (assert_iden_spec_parametric Word256 _ _ R) as HAH.
  pose proof (assert_iden_spec_parametric blinding_entropy_value_type _ _ R) as HAB.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  pose proof (sha256_ctx8_init_spec_parametric _ _ RC) as HI.
  unfold elements_single_issuance_payload_spec. cbv zeta.
  solve [repeat first [exact HAA | exact HB | exact H32 | exact HF | exact HAT |
    exact HAH | exact HAB | exact HI | apply (Alg.comp_Parametric RC) |
    apply (Alg.pair_Parametric RC) | apply (Alg.take_Parametric RC) |
    apply (Alg.drop_Parametric RC) | apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_single_issuance_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (@elements_issuance_pair_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount alg)
      (AC.pair
        (@elements_issuance_pair_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount alg)
        (AC.pair
          (AC.pair (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)
            (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof))
          (@elements_issuance_blinding_entropy_spec alg))))
    (AC.case (AC.injl AC.unit) (AC.injr (@elements_single_issuance_payload_spec term))).

Lemma elements_single_issuance_hash_parametric : EFP.Parametric (@elements_single_issuance_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (@elements_issuance_pair_spec_parametric (@elements_issuance_asset_spec)
    Elements.IssuanceAssetAmount elements_issuance_asset_spec_parametric alg1 alg2 R) as HA.
  pose proof (@elements_issuance_pair_spec_parametric (@elements_issuance_token_spec)
    Elements.IssuanceTokenAmount elements_issuance_token_spec_parametric alg1 alg2 R) as HT.
  pose proof (elements_issuance_blinding_entropy_spec_parametric alg1 alg2 R) as HB.
  destruct R as [R [HAs [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HAs).
  pose proof (elements_single_issuance_payload_parametric _ _ RA) as HPL.
  destruct HAs as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_single_issuance_hash_spec. cbv zeta.
  solve [repeat first [exact HA | exact HT | exact HB | exact HPL | apply HP |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) |
    apply (Alg.injr_Parametric RC) | apply Alg.unit_Parametric]].
Qed.

Definition elements_single_issuance_bytes (a t : Ty.tySem issuance_asset_amount_value_type)
    (s r : Ty.tySem Word256) (b : Ty.tySem blinding_entropy_value_type) : list (Ty.tySem Word8) :=
  (((issuance_asset_amount_bytes a ++ issuance_asset_amount_bytes t) ++ vector_values Word8 5 s) ++
    vector_values Word8 5 r) ++ blinding_entropy_bytes b.

Lemma elements_single_issuance_bytes_bound a t s r b :
  Z.of_nat (length (elements_single_issuance_bytes a t s r b)) <= 261.
Proof.
  unfold elements_single_issuance_bytes. rewrite !app_length, !Nat2Z.inj_add, !vector_values_length.
  pose proof (issuance_asset_amount_bytes_bound a).
  pose proof (issuance_asset_amount_bytes_bound t).
  pose proof (blinding_entropy_bytes_bound b).
  change (Z.of_nat (length (issuance_asset_amount_bytes a)) +
    Z.of_nat (length (issuance_asset_amount_bytes t)) + 32 + 32 +
    Z.of_nat (length (blinding_entropy_bytes b)) <= 261). lia.
Qed.

Lemma elements_single_issuance_payload_option a t s r b :
  @elements_single_issuance_payload_spec optalg (a, (inr t, ((inr s, inr r), inr b))) =
    Some (from_hash256 (sha256_bytes_of (elements_single_issuance_bytes a t s r b))).
Proof.
  destruct (init_hash_sem (elements_single_issuance_bytes a t s r b)) as (cf & HAdd & HFin).
  { apply Z.le_lt_trans with (m := 261 / 64).
    - apply Z.div_le_mono; [lia|apply elements_single_issuance_bytes_bound].
    - vm_compute; reflexivity. }
  unfold elements_single_issuance_bytes in HAdd.
  destruct (add_app_some _ _ _ _ HAdd) as (c4 & E4 & EB).
  destruct (add_app_some _ _ _ _ E4) as (c3 & E3 & ER).
  destruct (add_app_some _ _ _ _ E3) as (c2 & E2 & ES).
  destruct (add_app_some _ _ _ _ E2) as (c1 & EA & ET).
  unfold elements_single_issuance_payload_spec. cbv zeta.
  opt_steps. rewrite opt_unit. cbv beta iota.
  rewrite (opt_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric tt).
  opt_steps. rewrite issuance_asset_amount_absorb_option. use_add EA.
  opt_steps. rewrite !assert_iden_option. cbv beta iota.
  rewrite issuance_asset_amount_absorb_option. use_add ET.
  opt_steps. rewrite (ctx8_addn_option 5). use_add ES.
  opt_steps. rewrite (ctx8_addn_option 5). use_add ER.
  opt_steps. rewrite literal_blinding_entropy_hash_option. use_add EB.
  exact HFin.
Qed.

Lemma elements_single_issuance_hash_some i e a t s r b :
  @elements_issuance_pair_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount
    elements_hash_alg i e = Some (inr a) ->
  @elements_issuance_pair_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount
    elements_hash_alg i e = Some (inr t) ->
  Elements.sem Elements.IssuanceAssetProof i e = Some (inr s) ->
  Elements.sem Elements.IssuanceTokenProof i e = Some (inr r) ->
  @elements_issuance_blinding_entropy_spec elements_hash_alg i e = Some (inr b) ->
  @elements_single_issuance_hash_spec elements_hash_alg i e =
    Some (inr (from_hash256 (sha256_bytes_of (elements_single_issuance_bytes a t s r b)))).
Proof.
  intros HA HT HS HR HB. unfold elements_single_issuance_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HA, HT, HS, HR, HB.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd]. rewrite (hr_injr Elements.env).
  rewrite (hr_assert Elements.env (fun term => @elements_single_issuance_payload_spec term)
    elements_single_issuance_payload_parametric).
  change (option_map (@inr Datatypes.unit (Ty.tySem Word256))
    (@elements_single_issuance_payload_spec optalg (a, (inr t, ((inr s, inr r), inr b)))) =
    Some (inr (from_hash256 (sha256_bytes_of (elements_single_issuance_bytes a t s r b))))).
  exact (f_equal (option_map (@inr Datatypes.unit (Ty.tySem Word256)))
    (elements_single_issuance_payload_option a t s r b)).
Qed.

Lemma elements_single_issuance_hash_none i e t s r b :
  @elements_issuance_pair_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount
    elements_hash_alg i e = Some (inl tt) ->
  @elements_issuance_pair_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount
    elements_hash_alg i e = Some t ->
  Elements.sem Elements.IssuanceAssetProof i e = Some s ->
  Elements.sem Elements.IssuanceTokenProof i e = Some r ->
  @elements_issuance_blinding_entropy_spec elements_hash_alg i e = Some b ->
  @elements_single_issuance_hash_spec elements_hash_alg i e = Some (inl tt).
Proof.
  intros HA HT HS HR HB. unfold elements_single_issuance_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HA, HT, HS, HR, HB.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd].
  rewrite (hr_injl Elements.env), (hr_unit Elements.env). reflexivity.
Qed.

Definition elements_single_issuance_result (e : Elements.env) (i : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i)) with
  | None => inl tt
  | Some txi => inr (from_hash256 (sha256_bytes_of (elements_single_issuance_bytes
      (issuance_asset_pair_of_input txi) (issuance_token_pair_of_input txi)
      (from_hash256 (byteStringHash (issuance_asset_proof_bytes txi)))
      (from_hash256 (byteStringHash (issuance_token_proof_bytes txi)))
      (elements_blinding_entropy_of_input txi))))
  end.

Lemma elements_single_issuance_hash_sem i e :
  @elements_single_issuance_hash_spec elements_hash_alg i e = Some (elements_single_issuance_result e i).
Proof.
  pose proof (elements_issuance_asset_pairs_sem i e) as HA.
  pose proof (elements_issuance_token_pairs_sem i e) as HT.
  pose proof (elements_blinding_entropies_sem i e) as HB.
  unfold elements_issuance_asset_pairs, elements_issuance_token_pairs, elements_blinding_entropies in HA, HT, HB.
  rewrite nth_error_map in HA, HT, HB. unfold wz in HA, HT, HB.
  unfold elements_single_issuance_result.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi|] eqn:HE;
    cbn [option_map] in HA, HT, HB.
  - apply elements_single_issuance_hash_some; [exact HA|exact HT| | |exact HB];
      unfold Elements.sem; cbv zeta; rewrite HE; reflexivity.
  - apply elements_single_issuance_hash_none with (t := inl tt) (s := inl tt) (r := inl tt) (b := inl tt);
      [exact HA|exact HT| | |exact HB]; unfold Elements.sem; cbv zeta; rewrite HE; reflexivity.
Qed.
