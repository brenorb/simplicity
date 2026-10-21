(** Original C issuance amount cache getters against the complete indexed
    primitive program. Initial cache correspondence remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_forWhile_seq C.jet_sha_ctx8_spec.
Require Import C.jet_sha_hash_loop_gen C.jet_bitcoin_tx_hash.
Require Import C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program C.jet_elements_prim_sem.
Require Import C.jet_elements_issuance_entropy_spec C.jet_elements_issuance_amount_hash_spec.
Require Import C.jet_elements_amount_jets.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition issuance_pair_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option issuance_amount_option)
      (Ty.Sum Ty.Unit issuance_asset_amount_value_type) :=
  AC.case (AC.injl AC.unit)
    (AC.case (AC.injr (AC.injl AC.unit))
      (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
        (AC.case (AC.injl AC.unit)
          (AC.case (AC.injl AC.unit)
            (AC.injr (AC.injr (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))))))).

Lemma issuance_pair_route_parametric : Alg.Core.Parametric (@issuance_pair_route).
Proof.
  intros alg1 alg2 R. unfold issuance_pair_route.
  solve [repeat first [apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_issuance_pair_spec
    (g : forall alg : EFP.Algebra, EFP.domain alg Word32 issuance_digest_option)
    (pm : Elements.t Word32 issuance_amount_option) {alg : EFP.Algebra} :
    EFP.domain alg Word32 (Ty.Sum Ty.Unit issuance_asset_amount_value_type) :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @AC.comp _ _ _ core (@AC.pair _ _ _ core (g alg) (@EFP.Combinators.prim _ _ alg pm))
    (@issuance_pair_route core).

Lemma elements_issuance_pair_spec_parametric g pm (Hg : EFP.Parametric g) :
  EFP.Parametric (@elements_issuance_pair_spec g pm).
Proof.
  intros alg1 alg2 R. pose proof (Hg alg1 alg2 R) as HG.
  destruct R as [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_pair_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [exact HG | apply HP].
  - exact (issuance_pair_route_parametric _ _ RC).
Qed.

Lemma elements_issuance_pair_spec_sem g pm i e :
  @elements_issuance_pair_spec g pm elements_hash_alg i e =
    match g elements_hash_alg i e, Elements.sem pm i e with
    | Some h, Some a => Some (@issuance_pair_route Alg.CoreFunSem (h, a))
    | _, _ => None
    end.
Proof.
  unfold elements_issuance_pair_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), elements_hash_prim.
  destruct (g elements_hash_alg i e), (Elements.sem pm i e); [|reflexivity..].
  apply (hr_core Elements.env (@issuance_pair_route) issuance_pair_route_parametric).
Qed.

Definition issuance_asset_pair_of_input (txi : sigTxInput) :
    Ty.tySem issuance_asset_amount_value_type :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) =>
      match issuance_asset_of_input txi with
      | inr h => inr (h, encode_amount (clearPrf (newIssuanceAmount new)))
      | inl _ => inl tt
      end
  | Some (inr re) =>
      match issuance_asset_of_input txi with
      | inr h => inr (h, encode_amount (clearPrf (reissuanceAmount re)))
      | inl _ => inl tt
      end
  end.

Definition elements_issuance_asset_pairs (e : Elements.env) :
    list (Ty.tySem issuance_asset_amount_value_type) :=
  map issuance_asset_pair_of_input (sigTxIn (Elements.envTx e)).

Lemma elements_issuance_asset_pairs_sem i e :
  @elements_issuance_pair_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount
    elements_hash_alg i e =
  Some (match nth_error (elements_issuance_asset_pairs e) (Z.to_nat (wz 5 i)) with
        | Some x => inr x | None => inl tt end).
Proof.
  rewrite elements_issuance_pair_spec_sem, elements_issuance_asset_sem.
  unfold Elements.sem, issuance_asset_result, elements_issuance_asset_pairs, wz.
  rewrite nth_error_map.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi|];
    [|reflexivity].
  destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
    cbn [option_map];
    unfold issuance_asset_pair_of_input, issuance_asset_of_input, issuance_entropy_of_input;
    rewrite HI; reflexivity.
Qed.

Definition issuance_token_pair_of_input (txi : sigTxInput) :
    Ty.tySem issuance_asset_amount_value_type :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) =>
      match issuance_token_of_input txi with
      | inr h => inr (h, encode_amount (clearPrf (newIssuanceTokenAmount new)))
      | inl _ => inl tt
      end
  | Some (inr re) =>
      match issuance_token_of_input txi with
      | inr h => inr (h, encode_amount (Explicit Int64.zero))
      | inl _ => inl tt
      end
  end.

Definition elements_issuance_token_pairs (e : Elements.env) :
    list (Ty.tySem issuance_asset_amount_value_type) :=
  map issuance_token_pair_of_input (sigTxIn (Elements.envTx e)).

Lemma elements_issuance_token_pairs_sem i e :
  @elements_issuance_pair_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount
    elements_hash_alg i e =
  Some (match nth_error (elements_issuance_token_pairs e) (Z.to_nat (wz 5 i)) with
        | Some x => inr x | None => inl tt end).
Proof.
  rewrite elements_issuance_pair_spec_sem, elements_issuance_token_sem.
  unfold Elements.sem, issuance_token_result, elements_issuance_token_pairs, wz.
  rewrite nth_error_map.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi|];
    [|reflexivity].
  destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
    cbn [option_map];
    unfold issuance_token_pair_of_input, issuance_token_of_input;
    rewrite HI; reflexivity.
Qed.

Definition elements_issuance_amounts_hash_spec
    (g : forall alg : EFP.Algebra, EFP.domain alg Word32 issuance_digest_option)
    (pm : Elements.t Word32 issuance_amount_option) {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec issuance_asset_amount_value_type
    (fun term => @issuance_asset_amount_absorb_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@elements_issuance_pair_spec g pm alg)).

Lemma elements_issuance_amounts_hash_spec_parametric g pm (Hg : EFP.Parametric g) :
  EFP.Parametric (@elements_issuance_amounts_hash_spec g pm).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_issuance_pair_spec_parametric g pm Hg alg1 alg2 R) as HP.
  destruct R as [R [HA [HPrim]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_issuance_amounts_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ issuance_asset_amount_absorb_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). exact HP.
Qed.

Lemma elements_issuance_amounts_loop_bound : 66 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute; reflexivity. Qed.

Theorem elements_issuance_amounts_hash_spec_sem g pm
    (xs_of : Elements.env -> list (Ty.tySem issuance_asset_amount_value_type)) :
  (forall i e, @elements_issuance_pair_spec g pm elements_hash_alg i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None => inl tt end)) ->
  forall e, @elements_issuance_amounts_hash_spec g pm elements_hash_alg tt e =
    Some (from_hash256 (elems_hash_of issuance_asset_amount_value_type issuance_asset_amount_bytes 5 (xs_of e))).
Proof.
  intros HS e. unfold elements_issuance_amounts_hash_spec. cbv zeta.
  apply (hash_elems_reader_sem Elements.env issuance_asset_amount_value_type
    (fun term => @issuance_asset_amount_absorb_spec term) issuance_asset_amount_absorb_spec_parametric
    issuance_asset_amount_bytes issuance_asset_amount_absorb_option 5 _ e (xs_of e) 66).
  - intro i. apply HS.
  - exact issuance_asset_amount_bytes_bound.
  - lia.
  - exact elements_issuance_amounts_loop_bound.
Qed.

Definition elements_issuance_asset_amounts_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  @elements_issuance_amounts_hash_spec (@elements_issuance_asset_spec) Elements.IssuanceAssetAmount alg.
Definition elements_issuance_token_amounts_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  @elements_issuance_amounts_hash_spec (@elements_issuance_token_spec) Elements.IssuanceTokenAmount alg.

Definition elements_issuance_asset_amounts_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of issuance_asset_amount_value_type issuance_asset_amount_bytes 5 (elements_issuance_asset_pairs e).
Definition elements_issuance_token_amounts_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of issuance_asset_amount_value_type issuance_asset_amount_bytes 5 (elements_issuance_token_pairs e).

Theorem elements_issuance_asset_amounts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_asset_amounts_hash_of 0 472 760)
    (fun a e => @elements_issuance_asset_amounts_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuanceAssetAmountsHash).
  - exact (elements_issuance_amounts_hash_spec_sem (@elements_issuance_asset_spec)
      Elements.IssuanceAssetAmount elements_issuance_asset_pairs elements_issuance_asset_pairs_sem).
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

Theorem elements_issuance_token_amounts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_token_amounts_hash_of 0 504 760)
    (fun a e => @elements_issuance_token_amounts_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuanceTokenAmountsHash).
  - exact (elements_issuance_amounts_hash_spec_sem (@elements_issuance_token_spec)
      Elements.IssuanceTokenAmount elements_issuance_token_pairs elements_issuance_token_pairs_sem).
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
