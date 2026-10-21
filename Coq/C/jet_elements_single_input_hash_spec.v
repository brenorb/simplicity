(** Canonical Elements inputHash, including optional pegin and annex.
    This semantic bridge is support for the whole original C jet. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_words_hash_program.
Require Import C.jet_elements_outpoints_hash_program C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec.
Require Import C.jet_buffer_input C.jet_buffer_empty_spec C.jet_sha_add_buffer_spec.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_composite_hash C.jet_sha_hash_words_reader.
Require Import C.jet_bitcoin_tx_hash.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition elements_single_input_tail_type : Ty :=
  Ty.Prod (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))
    (Ty.Prod (Ty.Sum Ty.Unit Word32) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))).

Definition elements_single_input_payload_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod (Ty.Sum Ty.Unit Word256) elements_single_input_tail_type) Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair
      (AC.comp
        (AC.pair
          (AC.comp
            (AC.pair
              (AC.comp AC.unit (@sha256_ctx8_init_spec core))
              (AC.pair (AC.take AC.iden)
                (AC.drop (AC.take (@assert_iden_spec (Ty.Prod Word256 Word32) term)))))
            (@elements_outpoint_add_spec term))
          (AC.drop (AC.drop (AC.take (@assert_iden_spec Word32 term)))))
        (@ctx8_addn_spec 2 term))
      (AC.drop (AC.drop (AC.drop (@assert_iden_spec (Ty.Sum Ty.Unit Word256) term)))))
    (AC.comp (@annex_hash_spec term) (@ctx8_finalize_spec term)).

Lemma elements_single_input_payload_parametric :
  Alg.Assertion.Parametric (@elements_single_input_payload_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_outpoint_add_spec_parametric _ _ R) as HO.
  pose proof (ctx8_addn_spec_parametric 2 _ _ R) as H4.
  pose proof (ctx8_finalize_spec_parametric _ _ R) as HF.
  pose proof (annex_hash_spec_parametric _ _ R) as HA.
  pose proof (assert_iden_spec_parametric (Ty.Prod Word256 Word32) _ _ R) as HAO.
  pose proof (assert_iden_spec_parametric Word32 _ _ R) as HAS.
  pose proof (assert_iden_spec_parametric (Ty.Sum Ty.Unit Word256) _ _ R) as HAA.
  destruct R as [R [HC HA0]]. set (RC := Alg.Core.Parametric.Pack HC).
  pose proof (sha256_ctx8_init_spec_parametric _ _ RC) as HI.
  unfold elements_single_input_payload_spec. cbv zeta.
  solve [repeat first [exact HO | exact H4 | exact HF | exact HA | exact HAO |
    exact HAS | exact HAA | exact HI | apply (Alg.comp_Parametric RC) |
    apply (Alg.pair_Parametric RC) | apply (Alg.take_Parametric RC) |
    apply (Alg.drop_Parametric RC) | apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_single_input_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit Word256) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputPegin)
      (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputPrevOutpoint)
        (AC.pair (@EFP.Combinators.prim _ _ alg Elements.InputSequence)
          (@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash))))
    (AC.case (AC.injl AC.unit) (AC.injr (@elements_single_input_payload_spec term))).

Lemma elements_single_input_hash_parametric : EFP.Parametric (@elements_single_input_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (elements_single_input_payload_parametric _ _ RA) as HPL.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_single_input_hash_spec. cbv zeta.
  solve [repeat first [exact HPL | apply HP | apply (Alg.comp_Parametric RC) |
    apply (Alg.pair_Parametric RC) | apply (Alg.case_Parametric RC) |
    apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) | apply Alg.unit_Parametric]].
Qed.

Definition elements_single_input_bytes (pg : Ty.tySem (Ty.Sum Ty.Unit Word256))
    (op : Ty.tySem (Ty.Prod Word256 Word32)) (sq : Ty.tySem Word32)
    (ax : Ty.tySem (Ty.Sum Ty.Unit Word256)) : list (Ty.tySem Word8) :=
  (elements_outpoint_bytes (pg, op) ++ vector_values Word8 2 sq) ++ annex_elem_bytes ax.

Lemma elements_single_input_bytes_bound pg op sq ax :
  Z.of_nat (length (elements_single_input_bytes pg op sq ax)) <= 106.
Proof.
  unfold elements_single_input_bytes. rewrite !app_length, !Nat2Z.inj_add, vector_values_length.
  pose proof (elements_outpoint_bytes_bound (pg, op)).
  pose proof (annex_bytes_bound ax).
  change (Z.of_nat (length (elements_outpoint_bytes (pg, op))) + 4 +
    Z.of_nat (length (annex_elem_bytes ax)) <= 106). lia.
Qed.

Lemma elements_single_input_payload_option pg op sq ax :
  @elements_single_input_payload_spec optalg (pg, (inr op, (inr sq, inr ax))) =
    Some (from_hash256 (sha256_bytes_of (elements_single_input_bytes pg op sq ax))).
Proof.
  destruct (init_hash_sem (elements_single_input_bytes pg op sq ax)) as (cf & HAdd & HFin).
  { apply Z.le_lt_trans with (m := 106 / 64).
    - apply Z.div_le_mono; [lia|apply elements_single_input_bytes_bound].
    - vm_compute; reflexivity. }
  unfold elements_single_input_bytes in HAdd.
  destruct (add_app_some _ _ _ _ HAdd) as (c2 & E2 & EA).
  destruct (add_app_some _ _ _ _ E2) as (c1 & EO & ES).
  unfold elements_single_input_payload_spec. cbv zeta.
  opt_steps. rewrite opt_unit. cbv beta iota.
  rewrite (opt_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric tt).
  opt_steps. rewrite !assert_iden_option. cbv beta iota.
  rewrite elements_outpoint_add_option. use_add EO.
  opt_steps. rewrite (ctx8_addn_option 2). use_add ES.
  opt_steps. rewrite annex_hash_option. use_add EA.
  exact HFin.
Qed.

Lemma elements_single_input_hash_some i e pg op sq ax :
  Elements.sem Elements.InputPegin i e = Some (inr pg) ->
  Elements.sem Elements.InputPrevOutpoint i e = Some (inr op) ->
  Elements.sem Elements.InputSequence i e = Some (inr sq) ->
  Elements.sem Elements.InputAnnexHash i e = Some (inr ax) ->
  @elements_single_input_hash_spec elements_hash_alg i e =
    Some (inr (from_hash256 (sha256_bytes_of (elements_single_input_bytes pg op sq ax)))).
Proof.
  intros HP HO HS HA. unfold elements_single_input_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HP, HO, HS, HA.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd]. rewrite (hr_injr Elements.env).
  rewrite (hr_assert Elements.env (fun term => @elements_single_input_payload_spec term)
    elements_single_input_payload_parametric).
  change (option_map (@inr Datatypes.unit (Ty.tySem Word256))
    (@elements_single_input_payload_spec optalg (pg, (inr op, (inr sq, inr ax)))) =
    Some (inr (from_hash256 (sha256_bytes_of (elements_single_input_bytes pg op sq ax))))).
  exact (f_equal (option_map (@inr Datatypes.unit (Ty.tySem Word256)))
    (elements_single_input_payload_option pg op sq ax)).
Qed.

Lemma elements_single_input_hash_none i e op sq ax :
  Elements.sem Elements.InputPegin i e = Some (inl tt) ->
  Elements.sem Elements.InputPrevOutpoint i e = Some op ->
  Elements.sem Elements.InputSequence i e = Some sq ->
  Elements.sem Elements.InputAnnexHash i e = Some ax ->
  @elements_single_input_hash_spec elements_hash_alg i e = Some (inl tt).
Proof.
  intros HP HO HS HA. unfold elements_single_input_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim, HP, HO, HS, HA.
  cbv beta iota. rewrite (hr_case Elements.env). cbn [fst snd].
  rewrite (hr_injl Elements.env), (hr_unit Elements.env). reflexivity.
Qed.

Definition elements_single_input_result (e : Elements.env) (i : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i)) with
  | None => inl tt
  | Some txi => inr (from_hash256 (sha256_bytes_of (elements_single_input_bytes
      (match sigTxiPegin txi with None => inl tt | Some h => inr (from_hash256 h) end)
      (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
        @fromZ (WordToZ 5) (compcert.lib.Integers.Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))))
      (@fromZ (WordToZ 5) (compcert.lib.Integers.Int.unsigned (sigTxiSequence txi)))
      (match sigTxiAnnex txi with None => inl tt | Some bs => inr (from_hash256 (byteStringHash bs)) end))))
  end.

Lemma elements_single_input_hash_sem i e :
  @elements_single_input_hash_spec elements_hash_alg i e = Some (elements_single_input_result e i).
Proof.
  unfold elements_single_input_result.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi|] eqn:HE.
  - apply elements_single_input_hash_some;
      unfold Elements.sem; cbv zeta; rewrite HE; cbn [option_map];
      try reflexivity; destruct (sigTxiPegin txi); destruct (sigTxiAnnex txi); reflexivity.
  - apply elements_single_input_hash_none with (op := inl tt) (sq := inl tt) (ax := inl tt);
      unfold Elements.sem; cbv zeta; rewrite HE; reflexivity.
Qed.
