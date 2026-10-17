(** Original issuance_blinding_entropy_hash C getter and its full Simplicity
    program: three primitives, indexed traversal, byte absorption, finalize. *)
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
Require Import C.jet_elements_words_hash_program C.jet_elements_blinding_entropy_spec.
Require Import C.jet_elements_blinding_entropy_hash_spec.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_issuance_blinding_entropy_hash_spec {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec blinding_entropy_value_type (fun term => @blinding_entropy_hash_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@elements_issuance_blinding_entropy_spec alg)).

Lemma elements_issuance_blinding_entropy_hash_spec_parametric :
  EFP.Parametric (@elements_issuance_blinding_entropy_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_issuance_blinding_entropy_spec_parametric alg1 alg2 R) as HP.
  destruct R as [R [HA [HPrim]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_issuance_blinding_entropy_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ blinding_entropy_hash_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). exact HP.
Qed.

Lemma elements_blinding_entropy_loop_bound : 65 * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute; reflexivity. Qed.

Definition elements_issuance_blinding_entropy_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of blinding_entropy_value_type blinding_entropy_bytes 5 (elements_blinding_entropies e).

Theorem elements_issuance_blinding_entropy_hash_spec_sem e :
  @elements_issuance_blinding_entropy_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_issuance_blinding_entropy_hash_of e)).
Proof.
  unfold elements_issuance_blinding_entropy_hash_spec, elements_issuance_blinding_entropy_hash_of. cbv zeta.
  apply (hash_elems_reader_sem Elements.env blinding_entropy_value_type
    (fun term => @blinding_entropy_hash_spec term) blinding_entropy_hash_spec_parametric
    blinding_entropy_bytes blinding_entropy_hash_option 5 _ e (elements_blinding_entropies e) 65).
  - intros i. exact (elements_blinding_entropies_sem i e).
  - exact blinding_entropy_bytes_bound.
  - lia.
  - exact elements_blinding_entropy_loop_bound.
Qed.

Theorem elements_issuance_blinding_entropy_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_blinding_entropy_hash
    elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_issuance_blinding_entropy_hash_of 0 568 760)
    (fun a e => @elements_issuance_blinding_entropy_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _issuanceBlindingEntropyHash).
  - exact elements_issuance_blinding_entropy_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
