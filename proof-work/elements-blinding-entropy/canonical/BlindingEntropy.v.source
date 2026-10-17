(** Final original-C theorem using the literal Arith.one word8 program in
    the canonical blindingEntropyHash, rather than a replacement constant. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_spec C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_forWhile_seq C.jet_sha_ctx8_spec C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_sha_add_buffer_spec.
Require Import C.jet_sha_hash_loop_gen C.jet_bitcoin_tx_hash.
Require Import C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program C.jet_elements_blinding_entropy_spec.
Require Import C.jet_elements_blinding_entropy_hash_spec C.jet_elements_blinding_entropy_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_blinding_one8_option :
  @one8_spec (Alg.Assertion.toCore optalg) tt = Some byte_one.
Proof.
  rewrite (opt_core (@one8_spec) one8_spec_parametric tt), one8_spec_correct.
  reflexivity.
Qed.

Definition literal_blinding_entropy_hash_spec {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type blinding_entropy_value_type) sha256_ctx8_type :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
    (@AC.case _ _ _ _ core
      (AC.drop (@AC.comp _ _ _ core
        (AC.pair AC.iden (AC.comp AC.unit (@Word.zero 3 core))) (@ctx8_add1_spec term)))
      (@AC.comp _ _ _ core
        (AC.pair
          (AC.drop (@AC.comp _ _ _ core
            (AC.pair AC.iden (AC.comp AC.unit (@one8_spec core))) (@ctx8_add1_spec term)))
          (AC.take AC.iden))
        (@ctx8_addn_spec 6 term))).

Lemma literal_blinding_entropy_hash_spec_parametric :
  Alg.Assertion.Parametric (@literal_blinding_entropy_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (ctx8_add1_spec_parametric _ _ R) as H1.
  pose proof (ctx8_addn_spec_parametric 6 _ _ R) as H6.
  destruct R as [R [HC HA]]. set (RC := Alg.Core.Parametric.Pack HC).
  pose proof (one8_spec_parametric _ _ RC) as HO.
  unfold literal_blinding_entropy_hash_spec. cbv zeta.
  solve [repeat first [exact H1 | exact H6 | exact HO | apply (Word.zero_Parametric RC) |
    apply (Alg.comp_Parametric RC) | apply (Alg.pair_Parametric RC) |
    apply (Alg.case_Parametric RC) | apply (Alg.take_Parametric RC) |
    apply (Alg.drop_Parametric RC) | apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Lemma literal_blinding_entropy_hash_option c v :
  @literal_blinding_entropy_hash_spec optalg (c, v) = ctx8_add_list c (blinding_entropy_bytes v).
Proof.
  assert (HZ : @Word.zero 3 (Alg.Assertion.toCore optalg) tt = Some byte_zero).
  { exact (opt_core (fun alg => @Word.zero 3 alg)
      (fun a1 a2 R => @Word.zero_Parametric 3 a1 a2 R) tt). }
  unfold literal_blinding_entropy_hash_spec. cbv zeta. destruct v as [[] | p]; opt_steps.
  - rewrite opt_unit. cbv beta iota. rewrite HZ, ctx8_add1_option.
    cbn [blinding_entropy_bytes ctx8_add_list].
    destruct (ctx8_add1_model c byte_zero); reflexivity.
  - rewrite opt_unit. cbv beta iota. rewrite literal_blinding_one8_option, ctx8_add1_option.
    cbn [blinding_entropy_bytes ctx8_add_list].
    destruct (ctx8_add1_model c byte_one) as [c' | ]; [ | reflexivity].
    opt_steps. apply (ctx8_addn_option 6).
Qed.

Definition literal_issuance_blinding_entropy_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec blinding_entropy_value_type
    (fun term => @literal_blinding_entropy_hash_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@elements_issuance_blinding_entropy_spec alg)).

Lemma literal_issuance_blinding_entropy_hash_spec_parametric :
  EFP.Parametric (@literal_issuance_blinding_entropy_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_issuance_blinding_entropy_spec_parametric alg1 alg2 R) as HP.
  destruct R as [R [HA [HPrim]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold literal_issuance_blinding_entropy_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ literal_blinding_entropy_hash_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). exact HP.
Qed.

Theorem literal_issuance_blinding_entropy_hash_spec_sem e :
  @literal_issuance_blinding_entropy_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_issuance_blinding_entropy_hash_of e)).
Proof.
  unfold literal_issuance_blinding_entropy_hash_spec, elements_issuance_blinding_entropy_hash_of. cbv zeta.
  apply (hash_elems_reader_sem Elements.env blinding_entropy_value_type
    (fun term => @literal_blinding_entropy_hash_spec term) literal_blinding_entropy_hash_spec_parametric
    blinding_entropy_bytes literal_blinding_entropy_hash_option 5 _ e (elements_blinding_entropies e) 65).
  - intros i. exact (elements_blinding_entropies_sem i e).
  - exact blinding_entropy_bytes_bound.
  - lia.
  - exact elements_blinding_entropy_loop_bound.
Qed.

Theorem elements_issuance_blinding_entropy_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_blinding_entropy_hash
    elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 568 760)
    (fun a e => @literal_issuance_blinding_entropy_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuanceBlindingEntropyHash).
  - exact literal_issuance_blinding_entropy_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
