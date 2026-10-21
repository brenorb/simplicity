(** Canonical issuanceAssetAmountHash serializer: two null bytes when absent;
    otherwise an explicit asset id followed by the confidential/explicit amount.
    This is shared by the asset-amount and token-amount traversals. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_add_buffer_spec C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_elements_asset_amount_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition issuance_asset_amount_value_type : Ty :=
  Ty.Sum Ty.Unit (Ty.Prod Word256 elements_amount_hash_type).

Definition issuance_asset_amount_absorb_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type issuance_asset_amount_value_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ core
      (@AC.comp _ _ _ core
        (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (@Word.zero 4 core)))
        (@ctx8_addn_spec 1 term))
      (@AC.comp _ _ _ core
        (AC.pair (AC.drop AC.iden)
          (AC.pair (AC.injr (AC.take (AC.take AC.iden))) (AC.take (AC.drop AC.iden))))
        (@elements_asset_amount_hash_spec term))).

Lemma issuance_asset_amount_absorb_spec_parametric :
  Alg.Assertion.Parametric (@issuance_asset_amount_absorb_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_addn_spec_parametric 1 _ _ R) as H1.
  pose proof (elements_asset_amount_hash_spec_parametric _ _ R) as HAmount.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold issuance_asset_amount_absorb_spec. cbv zeta.
  solve [repeat first [exact H1 | exact HAmount | apply (Word.zero_Parametric RC) |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.injr_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition issuance_asset_amount_bytes (v : Ty.tySem issuance_asset_amount_value_type) :
    list (Ty.tySem Word8) :=
  match v with
  | inl _ => [byte_zero; byte_zero]
  | inr (asset, amount) => elements_asset_amount_bytes (inr asset, amount)
  end.

Lemma issuance_asset_amount_absorb_option c v :
  @issuance_asset_amount_absorb_spec optalg (c, v) =
    ctx8_add_list c (issuance_asset_amount_bytes v).
Proof.
  assert (HZ : @Word.zero 4 (Alg.Assertion.toCore optalg) tt =
    Some ((byte_zero, byte_zero) : Ty.tySem (Word 4))).
  { exact (opt_core (fun alg => @Word.zero 4 alg)
      (fun a1 a2 R => @Word.zero_Parametric 4 a1 a2 R) tt). }
  unfold issuance_asset_amount_absorb_spec. cbv zeta.
  destruct v as [[] | [a m]]; opt_steps.
  - rewrite opt_unit. cbv beta iota. rewrite HZ.
    rewrite (ctx8_addn_option 1). reflexivity.
  - apply elements_asset_amount_hash_option.
Qed.

Lemma issuance_asset_amount_bytes_bound v :
  Z.of_nat (length (issuance_asset_amount_bytes v)) <= 66.
Proof.
  destruct v as [[] | [a m]]; cbn [issuance_asset_amount_bytes].
  - change (2 <= 66). lia.
  - apply elements_asset_amount_bytes_bound.
Qed.
