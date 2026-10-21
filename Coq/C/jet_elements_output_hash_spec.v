(** Canonical outputHash: amount/asset, nonce, script and range-proof lookups,
    with the same assertions and left-to-right serializers as SigHash.hs.
    This program is support for the actual C endpoint, not its proof alone. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_amount_jets C.jet_elements_asset_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_nonce_hash_spec.
Require Import C.jet_elements_words_hash_program C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec.
Require Import C.jet_buffer_input C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_composite_hash.
Require Import C.jet_sha_finalize_spec C.jet_buffer_empty_spec.
Require Import C.jet_sha_add_buffer_spec.
Require Import C.jet_sha_hash_words_reader C.jet_elements_indexed_ptr_jets C.jet_elements_output_proof_jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition elements_output_hash_tail_type : Ty :=
  Ty.Prod (Ty.Sum Ty.Unit elements_nonce_type)
    (Ty.Prod (Ty.Sum Ty.Unit Word256) (Ty.Sum Ty.Unit Word256)).

Definition elements_output_hash_payload_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod elements_asset_amount_type elements_output_hash_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp
                (AC.pair (AC.comp AC.unit (@sha256_ctx8_init_spec core)) (AC.take AC.iden))
                (@elements_asset_amount_hash_spec term))
              (AC.drop (AC.take (@assert_iden_spec elements_nonce_type term))))
            (@elements_nonce_hash_spec term))
          (AC.drop (AC.drop (AC.take (@assert_iden_spec Word256 term)))))
        (@ctx8_addn_spec 5 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec Word256 term)))))
    (AC.comp (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma elements_output_hash_payload_parametric :
  Alg.Assertion.Parametric (@elements_output_hash_payload_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_asset_amount_hash_spec_parametric _ _ R) as HAsset.
  pose proof (elements_nonce_hash_spec_parametric _ _ R) as HNonce.
  pose proof (ctx8_addn_spec_parametric 5 _ _ R) as H5.
  pose proof (ctx8_finalize_spec_parametric _ _ R) as HFin.
  pose proof (assert_iden_spec_parametric elements_nonce_type _ _ R) as HAssertNonce.
  pose proof (assert_iden_spec_parametric Word256 _ _ R) as HAssertHash.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  pose proof (sha256_ctx8_init_spec_parametric _ _ RC) as HInit.
  unfold elements_output_hash_payload_spec. cbv zeta.
  solve [repeat first [exact HAsset | exact HNonce | exact H5 | exact HFin |
    exact HAssertNonce | exact HAssertHash | exact HInit |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_output_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair (@elements_output_amount_spec alg)
      (AC.pair (@EFP.Combinators.prim _ _ alg Elements.OutputNonce)
        (AC.pair (@EFP.Combinators.prim _ _ alg Elements.OutputScriptHash)
          (@EFP.Combinators.prim _ _ alg Elements.OutputRangeProof))))
    (AC.case (AC.injl AC.unit) (AC.injr (@elements_output_hash_payload_spec term))).

Lemma elements_output_hash_spec_parametric : EFP.Parametric (@elements_output_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (elements_output_hash_payload_parametric _ _ RA) as HPayload.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_output_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC).
    + unfold elements_output_amount_spec, elements_amount_pair_spec.
      solve [repeat first [apply HP | apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
        apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) |
        apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
        apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
    + apply (Alg.pair_Parametric RC); [apply HP|apply (Alg.pair_Parametric RC); apply HP].
  - apply (Alg.case_Parametric RC); [apply (Alg.injl_Parametric RC), Alg.unit_Parametric|].
    apply (Alg.injr_Parametric RC). exact HPayload.
Qed.

Definition elements_output_hash_bytes (a : Ty.tySem elements_asset_amount_type)
    (n : Ty.tySem elements_nonce_type) (s r : Ty.tySem Word256) :=
  ((elements_asset_amount_bytes a ++ elements_nonce_bytes n) ++ vector_values Word8 5 s) ++ vector_values Word8 5 r.

Lemma elements_output_hash_bytes_bound a n s r :
  Z.of_nat (length (elements_output_hash_bytes a n s r)) <= 163.
Proof.
  unfold elements_output_hash_bytes. rewrite !app_length, !Nat2Z.inj_add, !vector_values_length.
  pose proof (elements_asset_amount_bytes_bound a).
  pose proof (elements_nonce_bytes_bound n).
  change (Z.of_nat (length (elements_asset_amount_bytes a)) +
    Z.of_nat (length (elements_nonce_bytes n)) + 32 + 32 <= 163).
  lia.
Qed.

Lemma elements_output_hash_payload_option a n s r :
  @elements_output_hash_payload_spec optalg (a, (inr n, (inr s, inr r))) =
    Some (from_hash256 (sha256_bytes_of (elements_output_hash_bytes a n s r))).
Proof.
  destruct (init_hash_sem (elements_output_hash_bytes a n s r)) as (cf & HAdd & HFin).
  { apply Z.le_lt_trans with (m := 163 / 64).
    - apply Z.div_le_mono; [lia|apply elements_output_hash_bytes_bound].
    - vm_compute; reflexivity. }
  unfold elements_output_hash_bytes in HAdd.
  destruct (add_app_some _ _ _ _ HAdd) as (c3 & E3 & E4).
  destruct (add_app_some _ _ _ _ E3) as (c2 & E2 & ES).
  destruct (add_app_some _ _ _ _ E2) as (c1 & EA & EN).
  unfold elements_output_hash_payload_spec. cbv zeta.
  opt_steps. rewrite opt_unit. cbv beta iota.
  rewrite (opt_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric tt).
  opt_steps. rewrite elements_asset_amount_hash_option.
  use_add EA. opt_steps. rewrite !assert_iden_option. cbv beta iota.
  rewrite elements_nonce_hash_option. use_add EN.
  opt_steps. rewrite (ctx8_addn_option 5). use_add ES.
  opt_steps. rewrite (ctx8_addn_option 5). use_add E4.
  exact HFin.
Qed.

Lemma elements_output_hash_some i e a n s r :
  @elements_output_amount_spec elements_hash_alg i e = Some (inr a) ->
  Elements.sem Elements.OutputNonce i e = Some (inr n) ->
  Elements.sem Elements.OutputScriptHash i e = Some (inr s) ->
  Elements.sem Elements.OutputRangeProof i e = Some (inr r) ->
  @elements_output_hash_spec elements_hash_alg i e =
    Some (inr (from_hash256 (sha256_bytes_of (elements_output_hash_bytes a n s r)))).
Proof.
  intros HA HN HS HR. unfold elements_output_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HA, HN, HS, HR.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd]. rewrite (hr_injr Elements.env).
  rewrite (hr_assert Elements.env (fun term => @elements_output_hash_payload_spec term)
    elements_output_hash_payload_parametric).
  change (option_map (@inr Datatypes.unit (Ty.tySem Word256))
    (@elements_output_hash_payload_spec optalg (a, (inr n, (inr s, inr r)))) =
    Some (inr (from_hash256 (sha256_bytes_of (elements_output_hash_bytes a n s r))))).
  exact (f_equal (option_map (@inr Datatypes.unit (Ty.tySem Word256)))
    (elements_output_hash_payload_option a n s r)).
Qed.

Lemma elements_output_hash_none i e n s r :
  @elements_output_amount_spec elements_hash_alg i e = Some (inl tt) ->
  Elements.sem Elements.OutputNonce i e = Some n ->
  Elements.sem Elements.OutputScriptHash i e = Some s ->
  Elements.sem Elements.OutputRangeProof i e = Some r ->
  @elements_output_hash_spec elements_hash_alg i e = Some (inl tt).
Proof.
  intros HA HN HS HR. unfold elements_output_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HA, HN, HS, HR.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd].
  rewrite (hr_injl Elements.env), (hr_unit Elements.env). reflexivity.
Qed.

Definition elements_output_hash_result (e : Elements.env) (i : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i)) with
  | None => inl tt
  | Some txo => inr (from_hash256 (sha256_bytes_of (elements_output_hash_bytes
      (encode_asset (clearPrf (txoAsset txo)), encode_amount (clearPrf (txoAmount txo)))
      (encode_nonce (txoNonce txo))
      (from_hash256 (byteStringHash (txoScript txo)))
      (from_hash256 (byteStringHash (viewPrf (txoAmount txo)))))))
  end.

Lemma elements_output_hash_sem i e :
  @elements_output_hash_spec elements_hash_alg i e = Some (elements_output_hash_result e i).
Proof.
  unfold elements_output_hash_result.
  assert (HN : Elements.sem Elements.OutputNonce i e = Some (elements_output_nonce_result e i)).
  { exact (elements_output_nonce_sem e i). }
  assert (HS : Elements.sem Elements.OutputScriptHash i e = Some (elements_output_script_hash_result e i)).
  { exact (elements_output_script_hash_sem e i). }
  assert (HR : Elements.sem Elements.OutputRangeProof i e = Some (elements_output_range_proof_result e i)).
  { exact (elements_output_range_proof_sem e i). }
  unfold elements_output_nonce_result in HN.
  unfold elements_output_script_hash_result in HS.
  unfold elements_output_range_proof_result in HR.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))) as [txo|] eqn:HE.
  - apply elements_output_hash_some; [|exact HN|exact HS|exact HR].
    rewrite elements_output_amount_sem. unfold amount_pair_result. rewrite HE. reflexivity.
  - apply elements_output_hash_none with (n := inl tt) (s := inl tt) (r := inl tt);
      [|exact HN|exact HS|exact HR].
    rewrite elements_output_amount_sem. unfold amount_pair_result. rewrite HE. reflexivity.
Qed.
