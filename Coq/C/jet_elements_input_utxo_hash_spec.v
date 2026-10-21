(** Canonical inputUtxoHash composition from Elements.Programs.SigHash.
    The C endpoint will use this primitive-bearing program through the shared
    asset/amount byte bridge. This file alone is not a C equivalence theorem. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_elements_amount_jets C.jet_elements_words_hash_program.
Require Import C.jet_elements_asset_jets C.jet_elements_input_hash_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_buffer_input C.jet_buffer_empty_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha256_ctx8_init_spec C.jet_sha_finalize_spec.
Require Import C.jet_sha_hash_words_reader C.jet_bitcoin_composite_hash C.jet_bitcoin_vh_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition elements_input_utxo_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg (Word 5) (Ty.Sum Ty.Unit (Word 8)) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@elements_input_amount_spec alg) (@EFP.Combinators.prim _ _ alg Elements.InputScriptHash))
    (@AC.case _ _ _ _ core
      (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.injr _ _ _ core
        (@AC.comp _ _ _ core
          (@AC.pair _ _ _ core
            (@AC.comp _ _ _ core
              (@AC.pair _ _ _ core
                (@AC.comp _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
                (@AC.take _ _ _ core (@AC.iden _ core)))
              (@elements_asset_amount_hash_spec term))
            (@AC.drop _ _ _ core (@assert_iden_spec (Word 8) term)))
          (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term))))).

Lemma elements_input_utxo_hash_spec_parametric : EFP.Parametric (@elements_input_utxo_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (elements_asset_amount_hash_spec_parametric _ _ RA) as H3.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  pose proof (assert_iden_spec_parametric (Word 8) _ _ RA) as HAs.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_input_utxo_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  { apply (Alg.pair_Parametric RC); [|apply HP].
    unfold elements_input_amount_spec, elements_amount_pair_spec.
    solve [repeat first [apply HP | apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
      apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) |
      apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
      apply Alg.unit_Parametric | apply Alg.iden_Parametric]]. }
  apply (Alg.case_Parametric RC); [apply (Alg.injl_Parametric RC), Alg.unit_Parametric|].
  apply (Alg.injr_Parametric RC).
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|apply (Alg.drop_Parametric RC); exact HAs].
  apply (Alg.comp_Parametric RC); [|exact H3].
  apply (Alg.pair_Parametric RC); [|apply (Alg.take_Parametric RC), Alg.iden_Parametric].
  apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply (sha256_ctx8_init_spec_parametric _ _ RC)].
Qed.

Definition elements_input_utxo_bytes (v : Ty.tySem elements_asset_amount_type) (h : Ty.tySem (Word 8)) : list (Ty.tySem (Word 3)) :=
  elements_asset_amount_bytes v ++ vector_values (Word 3) 5 h.

Lemma elements_input_utxo_hash_none (i : Ty.tySem (Word 5)) e (oh : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) :
  @elements_input_amount_spec elements_hash_alg i e = Some (inl tt) ->
  @Elements.sem (Word 5) (Ty.Sum Ty.Unit (Word 8)) Elements.InputScriptHash i e = Some oh ->
  @elements_input_utxo_hash_spec elements_hash_alg i e = Some (inl tt).
Proof.
  intros Hv Hh. unfold elements_input_utxo_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), elements_hash_prim, Hv, Hh. cbv beta iota.
  rewrite (hr_case Elements.env). cbn [fst snd]. rewrite (hr_injl Elements.env), (hr_unit Elements.env). reflexivity.
Qed.

Lemma elements_input_utxo_hash_some (i : Ty.tySem (Word 5)) e v h :
  @elements_input_amount_spec elements_hash_alg i e = Some (inr v) ->
  @Elements.sem (Word 5) (Ty.Sum Ty.Unit (Word 8)) Elements.InputScriptHash i e = Some (inr h) ->
  @elements_input_utxo_hash_spec elements_hash_alg i e = Some (inr (from_hash256 (sha256_bytes_of (elements_input_utxo_bytes v h)))).
Proof.
  intros Hv Hh. unfold elements_input_utxo_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), elements_hash_prim, Hv, Hh. cbv beta iota.
  rewrite (hr_case Elements.env). cbn [fst snd]. rewrite (hr_injr Elements.env).
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env), (hr_unit Elements.env).
  rewrite (hr_core Elements.env (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite (hr_take Elements.env), (hr_iden Elements.env). cbn [fst snd].
  rewrite (hr_assert Elements.env (fun alg => @elements_asset_amount_hash_spec alg) elements_asset_amount_hash_spec_parametric), elements_asset_amount_hash_option.
  rewrite (hr_drop Elements.env). cbn [snd].
  rewrite (hr_assert Elements.env (fun alg => @assert_iden_spec (Word 8) alg) (assert_iden_spec_parametric (Word 8))),
    assert_iden_option.
  destruct (init_hash_sem (elements_input_utxo_bytes v h)) as (cf & H1 & H2).
  { unfold elements_input_utxo_bytes. rewrite app_length, vector_values_length, Nat2Z.inj_add.
    pose proof (elements_asset_amount_bytes_bound v).
    apply Z.le_lt_trans with (m := 98 / 64).
    - apply Z.div_le_mono; [lia|change (Z.of_nat (length (elements_asset_amount_bytes v)) + 32 <= 98); lia].
    - vm_compute; reflexivity. }
  unfold elements_input_utxo_bytes in H1.
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  use_add E2.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric), H2.
  reflexivity.
Qed.

Definition elements_input_utxo_hash_result (e : Elements.env) (i : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i)) with
  | None => inl tt
  | Some txi => inr (from_hash256 (sha256_bytes_of
      (elements_input_utxo_bytes
        (encode_asset (utxoAsset (sigTxiTxo txi)), encode_amount (utxoAmount (sigTxiTxo txi)))
        (from_hash256 (byteStringHash (utxo_script_bytes txi))))))
  end.

Lemma elements_input_utxo_hash_sem i e :
  @elements_input_utxo_hash_spec elements_hash_alg i e =
    Some (elements_input_utxo_hash_result e i).
Proof.
  unfold elements_input_utxo_hash_result.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi|] eqn:HN.
  - apply elements_input_utxo_hash_some.
    + rewrite elements_input_amount_sem. unfold amount_pair_result. rewrite HN. reflexivity.
    + change (@elements_input_script_hash_spec elements_hash_alg i e =
        Some (inr (from_hash256 (byteStringHash (utxo_script_bytes txi))))).
      rewrite elements_input_script_hash_sem. unfold elements_input_script_hash_result.
      rewrite HN. reflexivity.
  - apply elements_input_utxo_hash_none with (oh := inl tt).
    + rewrite elements_input_amount_sem. unfold amount_pair_result. rewrite HN. reflexivity.
    + change (@elements_input_script_hash_spec elements_hash_alg i e = Some (inl tt)).
      rewrite elements_input_script_hash_sem. unfold elements_input_script_hash_result.
      rewrite HN. reflexivity.
Qed.
