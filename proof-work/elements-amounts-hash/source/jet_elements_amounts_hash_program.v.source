(** Original input/output_amounts_hash C getters against the canonical
    Transaction amount-pair program and shared assetAmountHash/SHA loop. *)
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
Require Import C.jet_elements_words_hash_program C.jet_elements_amount_jets C.jet_elements_asset_jets.
Require Import C.jet_elements_asset_amount_hash_spec.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_amounts_hash_spec
    (pm : Elements.t Word32 (Ty.Sum Ty.Unit elements_amount_hash_type))
    (pa : Elements.t Word32 (Ty.Sum Ty.Unit elements_asset_hash_type))
    {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec elements_asset_amount_type (fun term => @elements_asset_amount_hash_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core
      (@elements_amount_pair_spec alg Word32 elements_amount_hash_type elements_asset_hash_type
        (@EFP.Combinators.prim _ _ alg pm) (@EFP.Combinators.prim _ _ alg pa))).

Lemma elements_amounts_hash_spec_parametric pm pa : EFP.Parametric (@elements_amounts_hash_spec pm pa).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_amounts_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ elements_asset_amount_hash_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). unfold elements_amount_pair_spec.
  solve [repeat first [apply HP | apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Lemma elements_amounts_loop_bound : 66 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute; reflexivity. Qed.

Theorem elements_amounts_hash_spec_sem pm pa
    (xs_of : Elements.env -> list (Ty.tySem elements_asset_amount_type)) :
  (forall i e,
    @elements_amount_pair_spec elements_hash_alg Word32 elements_amount_hash_type elements_asset_hash_type
      (@EFP.Combinators.prim _ _ elements_hash_alg pm) (@EFP.Combinators.prim _ _ elements_hash_alg pa) i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None => inl tt end)) ->
  forall e, @elements_amounts_hash_spec pm pa elements_hash_alg tt e =
    Some (from_hash256 (elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 (xs_of e))).
Proof.
  intros Hsem e. unfold elements_amounts_hash_spec. cbv zeta.
  apply (hash_elems_reader_sem Elements.env elements_asset_amount_type
    (fun term => @elements_asset_amount_hash_spec term) elements_asset_amount_hash_spec_parametric
    elements_asset_amount_bytes elements_asset_amount_hash_option 5 _ e (xs_of e) 66).
  - intros i. apply Hsem.
  - exact elements_asset_amount_bytes_bound.
  - lia.
  - exact elements_amounts_loop_bound.
Qed.

Theorem elements_tx_amounts_hash_jet pm pa xs_of (f : function) (field : ident) (hdelta : Z) :
  (forall i e,
    @elements_amount_pair_spec elements_hash_alg Word32 elements_amount_hash_type elements_asset_hash_type
      (@EFP.Combinators.prim _ _ elements_hash_alg pm) (@EFP.Combinators.prim _ _ elements_hash_alg pa) i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None => inl tt end)) ->
  elements_wrapper_shape f (elements_simple_rest (elements_hash_mid_writeHash _tx _elementsTransaction field)) ->
  elements_field_at _elementsTransaction field hdelta ->
  0 <= hdelta /\ hdelta + 32 <= 760 ->
  application_jet_local_spec_sep f elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 (xs_of e)) 0 hdelta 760)
    (fun a e => @elements_amounts_hash_spec pm pa elements_hash_alg a e).
Proof.
  intros HS HShape HField HRange.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := field).
  - exact (elements_amounts_hash_spec_sem pm pa xs_of HS).
  - exact HShape.
  - exact elements_txEnv_tx.
  - exact HField.
  - lia.
  - exact HRange.
Qed.

Definition elements_output_amounts_of (e : Elements.env) : list (Ty.tySem elements_asset_amount_type) :=
  map (fun txo => (encode_asset (clearPrf (txoAsset txo)), encode_amount (clearPrf (txoAmount txo))))
    (sigTxOut (Elements.envTx e)).

Lemma elements_output_amounts_of_sem i e :
  @elements_output_amount_spec elements_hash_alg i e =
    Some (match nth_error (elements_output_amounts_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None => inl tt end).
Proof.
  rewrite elements_output_amount_sem. unfold elements_output_amounts_of, amount_pair_result, wz.
  rewrite nth_error_map.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Definition elements_output_amounts_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @elements_amounts_hash_spec Elements.OutputAmount Elements.OutputAsset alg.
Definition elements_output_amounts_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 (elements_output_amounts_of e).

Theorem elements_output_amounts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_output_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_output_amounts_hash_of 0 24 760)
    (fun a e => @elements_output_amounts_hash_spec elements_hash_alg a e).
Proof.
  unfold elements_output_amounts_hash_of, elements_output_amounts_hash_spec.
  eapply elements_tx_amounts_hash_jet with (field := _outputAssetAmountsHash).
  - exact elements_output_amounts_of_sem.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_input_amounts_of (e : Elements.env) : list (Ty.tySem elements_asset_amount_type) :=
  map (fun txi => (encode_asset (utxoAsset (sigTxiTxo txi)), encode_amount (utxoAmount (sigTxiTxo txi))))
    (sigTxIn (Elements.envTx e)).

Lemma elements_input_amounts_of_sem i e :
  @elements_input_amount_spec elements_hash_alg i e =
    Some (match nth_error (elements_input_amounts_of e) (Z.to_nat (wz 5 i)) with Some x => inr x | None => inl tt end).
Proof.
  rewrite elements_input_amount_sem. unfold elements_input_amounts_of, amount_pair_result, wz.
  rewrite nth_error_map.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Definition elements_input_amounts_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @elements_amounts_hash_spec Elements.InputAmount Elements.InputAsset alg.
Definition elements_input_amounts_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of elements_asset_amount_type elements_asset_amount_bytes 5 (elements_input_amounts_of e).

Theorem elements_input_amounts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_amounts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_amounts_hash_of 0 248 760)
    (fun a e => @elements_input_amounts_hash_spec elements_hash_alg a e).
Proof.
  unfold elements_input_amounts_hash_of, elements_input_amounts_hash_spec.
  eapply elements_tx_amounts_hash_jet with (field := _inputAssetAmountsHash).
  - exact elements_input_amounts_of_sem.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.
