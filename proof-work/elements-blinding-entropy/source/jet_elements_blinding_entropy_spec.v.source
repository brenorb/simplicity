(** The canonical three-primitive issuanceBlindingEntropy program. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_elements_prim C.jet_elements_words_hash_program.
Require Import C.jet_sha_hash_words_reader C.jet_buffer_empty_spec C.jet_forWhile_seq.
Import ListNotations.
Set Default Timeout 10.

Definition blinding_digest_option : Ty := Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256).
Definition blinding_entropy_pair : Ty := Ty.Prod Word256 Word256.
Definition blinding_entropy_value_type : Ty := Ty.Sum Ty.Unit blinding_entropy_pair.
Definition blinding_entropy_result_type : Ty := Ty.Sum Ty.Unit blinding_entropy_value_type.

Definition blinding_entropy_body_spec {core : Alg.Core.Algebra} :
    core (Ty.Prod blinding_digest_option blinding_digest_option) blinding_entropy_result_type :=
  AC.case (AC.injl AC.unit)
    (AC.case (AC.injr (AC.injl AC.unit))
      (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
        (AC.case (AC.injl AC.unit)
          (AC.injr (AC.case (AC.injl AC.unit)
            (AC.injr (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))))))).

Lemma blinding_entropy_body_spec_parametric : Alg.Core.Parametric (@blinding_entropy_body_spec).
Proof.
  intros alg1 alg2 R. unfold blinding_entropy_body_spec.
  solve [repeat first [apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.unit_Parametric |
    apply Alg.iden_Parametric]].
Qed.

Definition blinding_entropy_body_value (blinding entropy : Ty.tySem blinding_digest_option) :
    Ty.tySem blinding_entropy_result_type :=
  match blinding with
  | inl _ => inl tt
  | inr (inl _) => inr (inl tt)
  | inr (inr b) =>
      match entropy with
      | inl _ => inl tt
      | inr (inl _) => inr (inl tt)
      | inr (inr h) => inr (inr (b, h))
      end
  end.

Lemma blinding_entropy_body_spec_value b h :
  @blinding_entropy_body_spec Alg.CoreFunSem (b, h) = blinding_entropy_body_value b h.
Proof.
  destruct b as [[] | [[] | b]]; destruct h as [[] | [[] | h]]; reflexivity.
Qed.

Definition blinding_entropy_route_spec {core : Alg.Core.Algebra} :
    core (Ty.Prod blinding_digest_option (Ty.Prod blinding_digest_option blinding_digest_option))
      blinding_entropy_result_type :=
  AC.case (AC.injl AC.unit)
    (AC.case (AC.drop (@blinding_entropy_body_spec core))
      (AC.injr (AC.injr (AC.pair (AC.comp AC.unit (@Word.zero 8 core)) (AC.take AC.iden))))).

Lemma blinding_entropy_route_spec_parametric : Alg.Core.Parametric (@blinding_entropy_route_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (blinding_entropy_body_spec_parametric alg1 alg2 R) as HB.
  unfold blinding_entropy_route_spec.
  solve [repeat first [exact HB | apply (Word.zero_Parametric R) | apply Alg.comp_Parametric |
    apply Alg.pair_Parametric | apply Alg.case_Parametric | apply Alg.injl_Parametric |
    apply Alg.injr_Parametric | apply Alg.take_Parametric | apply Alg.drop_Parametric |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Lemma blinding_entropy_route_spec_value contract b h :
  @blinding_entropy_route_spec Alg.CoreFunSem (contract, (b, h)) =
    match contract with
    | inl _ => inl tt
    | inr (inl _) => blinding_entropy_body_value b h
    | inr (inr c) => inr (inr (@Word.zero 8 Alg.CoreFunSem tt, c))
    end.
Proof.
  destruct contract as [[] | [[] | c]].
  - reflexivity.
  - exact (blinding_entropy_body_spec_value b h).
  - reflexivity.
Qed.

Lemma blinding_entropy_zero_word : @Word.zero 8 Alg.CoreFunSem tt = @fromZ (WordToZ 8) 0.
Proof. vm_compute; reflexivity. Qed.

Definition elements_issuance_blinding_entropy_spec {alg : EFP.Algebra} :
    EFP.domain alg Word32 blinding_entropy_result_type :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.NewIssuanceContract)
      (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.ReissuanceBlinding)
        (@EFP.Combinators.prim _ _ alg Elements.ReissuanceEntropy)))
    (@blinding_entropy_route_spec core).

Lemma elements_issuance_blinding_entropy_spec_parametric :
  EFP.Parametric (@elements_issuance_blinding_entropy_spec).
Proof.
  intros alg1 alg2 [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_blinding_entropy_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply HP | apply (Alg.pair_Parametric RC); apply HP].
  - exact (blinding_entropy_route_spec_parametric _ _ RC).
Qed.

Definition elements_blinding_entropy_of_input (txi : sigTxInput) : Ty.tySem blinding_entropy_value_type :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) => inr (@fromZ (WordToZ 8) 0, from_hash256 (newIssuanceContractHash new))
  | Some (inr re) => inr (from_hash256 (reissuanceBlindingNonce re), from_hash256 (reissuanceEntropy re))
  end.

Definition elements_blinding_entropies (e : Elements.env) : list (Ty.tySem blinding_entropy_value_type) :=
  map elements_blinding_entropy_of_input (sigTxIn (Elements.envTx e)).

Lemma elements_blinding_entropies_sem i e :
  @elements_issuance_blinding_entropy_spec elements_hash_alg i e =
    Some (match nth_error (elements_blinding_entropies e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold elements_issuance_blinding_entropy_spec, elements_blinding_entropies. cbv zeta.
  rewrite (hr_comp Elements.env), !(hr_pair Elements.env), !elements_hash_prim.
  unfold Elements.sem. cbv zeta.
  rewrite (hr_core Elements.env (@blinding_entropy_route_spec) blinding_entropy_route_spec_parametric).
  rewrite nth_error_map. unfold wz.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi | ]; [ | reflexivity].
  cbn [Datatypes.option_map elements_blinding_entropy_of_input].
  destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
    rewrite blinding_entropy_route_spec_value;
    unfold elements_blinding_entropy_of_input; rewrite HI;
    cbn [blinding_entropy_body_value Datatypes.option_map];
    try rewrite blinding_entropy_zero_word; reflexivity.
Qed.
