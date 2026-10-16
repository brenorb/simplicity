(** Literal Elements two-primitive issuance range-proof loop and original C.
    Reuse the generic counter/element reader loop, retaining both exits. *)
From Coq Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_forWhile_seq C.jet_forWhile_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_sha_add_buffer_spec C.jet_sha_hash_loop_gen.
Require Import C.jet_bitcoin_tx_hash C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma elements_issuance_proofs_bytes_bound (x : Ty.tySem Word512) :
  Z.of_nat (List.length (vector_values Word8 6 x)) <= 64.
Proof. rewrite vector_values_length. reflexivity. Qed.

Lemma elements_issuance_proofs_loop_bound : 64 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Definition elements_issuance_proofs_array {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod Ty.Unit Word32) (Ty.Sum Ty.Unit Word512) :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof))
      (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (@AC.unit _ core))
          (@AC.injr _ _ _ core (@AC.pair _ _ _ core (AC.drop AC.iden) (AC.take AC.iden)))))).

(** Same routing tree as the Haskell body, including both early exits. *)
Definition elements_issuance_proofs_body {alg : EFP.Algebra} :
    EFP.domain alg (Ty.Prod (Ty.Prod Ty.Unit Word32) sha256_ctx8_type)
      (Ty.Sum sha256_ctx8_type sha256_ctx8_type) :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)))
      (@AC.pair _ _ _ core
        (@AC.take _ _ _ core (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof)))
        (AC.drop AC.iden)))
    (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden))
          (@AC.pair _ _ _ core (AC.take AC.iden) (AC.drop (AC.drop AC.iden))))
        (@AC.case _ _ _ _ core (@AC.injl _ _ _ core (AC.drop (AC.drop AC.iden)))
          (@AC.injr _ _ _ core (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (AC.drop (AC.drop AC.iden))
              (@AC.pair _ _ _ core (AC.drop (AC.take AC.iden)) (AC.take AC.iden)))
            (@ctx8_addn_spec 6 term)))))).

Ltac elements_issuance_proofs_parametric_step RC HP :=
  first [apply HP | apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.injl_Parametric RC) | apply (Alg.injr_Parametric RC) |
    apply (Alg.take_Parametric RC) | apply (Alg.drop_Parametric RC) |
    apply Alg.unit_Parametric | apply Alg.iden_Parametric].

Lemma elements_issuance_proofs_array_parametric : EFP.Parametric (@elements_issuance_proofs_array).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_proofs_array. cbv zeta.
  solve [repeat elements_issuance_proofs_parametric_step RC HP].
Qed.

Lemma elements_issuance_proofs_body_parametric : EFP.Parametric (@elements_issuance_proofs_body).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof ((ctx8_addn_spec_parametric 6) _ _ RA) as HAdd.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_proofs_body. cbv zeta.
  solve [repeat first [exact HAdd | elements_issuance_proofs_parametric_step RC HP]].
Qed.

Definition elements_issuance_asset_proof_bytes (txi : sigTxInput) : list byte :=
  match sigTxiIssuance txi with
  | None => []
  | Some i => viewPrf (match i with
      | inl ni => newIssuanceAmount ni | inr ri => reissuanceAmount ri end)
  end.

Definition elements_issuance_token_proof_bytes (txi : sigTxInput) : list byte :=
  match sigTxiIssuance txi with
  | None => []
  | Some i => viewPrf (match i with
      | inl ni => newIssuanceTokenAmount ni | inr _ => Explicit Int64.zero end)
  end.

Definition elements_issuance_proofs_of (e : Elements.env) : list (Ty.tySem Word512) :=
  map (fun txi =>
    (from_hash256 (byteStringHash (elements_issuance_asset_proof_bytes txi)),
     from_hash256 (byteStringHash (elements_issuance_token_proof_bytes txi))))
    (sigTxIn (Elements.envTx e)).

Ltac elements_issuance_proofs_reader_steps :=
  repeat progress (cbv beta iota zeta; cbn [fst snd];
    rewrite ?(hr_comp Elements.env), ?(hr_pair Elements.env), ?(hr_take Elements.env),
      ?(hr_drop Elements.env), ?(hr_iden Elements.env), ?(hr_unit Elements.env),
      ?(hr_case Elements.env), ?(hr_injl Elements.env), ?(hr_injr Elements.env), ?elements_hash_prim).

Lemma elements_issuance_proofs_array_sem i e :
  @elements_issuance_proofs_array elements_hash_alg (tt, i) e =
    Some (match nth_error (elements_issuance_proofs_of e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_issuance_proofs_array, elements_issuance_proofs_of. cbv zeta.
  rewrite nth_error_map. elements_issuance_proofs_reader_steps.
  unfold Elements.sem, wz.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (@toZ (WordToZ 5) i))) as [txi | ];
    cbn [option_map]; elements_issuance_proofs_reader_steps;
    reflexivity.
Qed.

Lemma elements_issuance_proofs_body_reader_matches i c e :
  @elements_issuance_proofs_body elements_hash_alg ((tt, i), c) e =
    @gen_loop_body Word512 (fun term => @ctx8_addn_spec 6 term)
      (hash_reader_alg Elements.env) Ty.Unit Word32
      (@elements_issuance_proofs_array elements_hash_alg) ((tt, i), c) e.
Proof.
  unfold elements_issuance_proofs_body, gen_loop_body, elements_issuance_proofs_array. cbv zeta.
  elements_issuance_proofs_reader_steps. unfold Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (@toZ (WordToZ 5) i))) as [txi | ];
    cbn [option_map]; elements_issuance_proofs_reader_steps; reflexivity.
Qed.

Lemma elements_issuance_proofs_body_reader_eq :
  @elements_issuance_proofs_body elements_hash_alg =
    @gen_loop_body Word512 (fun term => @ctx8_addn_spec 6 term)
      (hash_reader_alg Elements.env) Ty.Unit Word32 (@elements_issuance_proofs_array elements_hash_alg).
Proof.
  apply functional_extensionality. intros [[[] i] c].
  apply functional_extensionality. intro e. apply elements_issuance_proofs_body_reader_matches.
Qed.

Definition elements_issuance_range_proofs_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core))
    (@AC.comp _ _ _ core
      (@for_while_program 5 _ _ _ core (@elements_issuance_proofs_body alg))
      (@AC.copair _ _ _ core (@ctx8_finalize_spec term) (@ctx8_finalize_spec term))).

Lemma elements_issuance_range_proofs_hash_spec_parametric : EFP.Parametric (@elements_issuance_range_proofs_hash_spec).
Proof.
  intros alg1 alg2 R. pose proof (elements_issuance_proofs_body_parametric _ _ R) as HBody.
  destruct R as [R [HA [HP]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_range_proofs_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply Alg.unit_Parametric | apply (sha256_ctx8_init_spec_parametric _ _ RC)].
  - apply (Alg.comp_Parametric RC).
    + apply (for_while_program_parametric 5 RC). exact HBody.
    + apply (Alg.copair_Parametric RC); exact HF.
Qed.

Lemma elements_issuance_range_proofs_hash_reader_program_matches :
  @elements_issuance_range_proofs_hash_spec elements_hash_alg =
    @hash_elems_spec Word512 (fun term => @ctx8_addn_spec 6 term) 5
      (hash_reader_alg Elements.env) (@elements_issuance_proofs_array elements_hash_alg).
Proof.
  unfold elements_issuance_range_proofs_hash_spec, hash_elems_spec, gen_loop_run. cbv zeta.
  rewrite elements_issuance_proofs_body_reader_eq. reflexivity.
Qed.

Definition elements_issuance_range_proofs_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of Word512 (vector_values Word8 6) 5 (elements_issuance_proofs_of e).

Theorem elements_issuance_range_proofs_hash_spec_sem e :
  @elements_issuance_range_proofs_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_issuance_range_proofs_hash_of e)).
Proof.
  rewrite elements_issuance_range_proofs_hash_reader_program_matches.
  apply (hash_elems_reader_sem Elements.env Word512
    (fun term => @ctx8_addn_spec 6 term) (ctx8_addn_spec_parametric 6)
    (vector_values Word8 6) (ctx8_addn_option 6) 5 _ e (elements_issuance_proofs_of e) 64).
  - intro i. exact (elements_issuance_proofs_array_sem i e).
  - apply elements_issuance_proofs_bytes_bound.
  - lia.
  - exact elements_issuance_proofs_loop_bound.
Qed.

Theorem elements_issuance_range_proofs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_range_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_range_proofs_hash_of 0 536 760)
    (fun a e => @elements_issuance_range_proofs_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuanceRangeProofsHash).
  - exact elements_issuance_range_proofs_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
