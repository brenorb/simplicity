(** The original Elements output_nonces_hash C cache getter against the
    primitive/nonceHash loop.  A missing output terminates iteration; a
    present output without a nonce contributes a zero byte instead. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_forWhile_seq C.jet_sha_ctx8_spec.
Require Import C.jet_sha_hash_loop_gen C.jet_bitcoin_tx_hash.
Require Import C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program C.jet_elements_nonce_hash_spec.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_output_nonces_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec elements_nonce_type (fun term => @elements_nonce_hash_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.OutputNonce)).

Lemma elements_output_nonces_hash_spec_parametric : EFP.Parametric (@elements_output_nonces_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_output_nonces_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ elements_nonce_hash_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). apply HP.
Qed.

Definition elements_nonce_encode (n : option nonce) : Ty.tySem elements_nonce_type :=
  match n with
  | None => inl tt
  | Some (inl (odd, w)) => inr (inl ((if odd then inr tt else inl tt), from_hash256 w))
  | Some (inr h) => inr (inr (from_hash256 h))
  end.

Definition elements_nonces_of (e : Elements.env) : list (Ty.tySem elements_nonce_type) :=
  map (fun txo => elements_nonce_encode (txoNonce txo)) (sigTxOut (Elements.envTx e)).

Lemma elements_nonces_of_sem i e :
  Elements.sem Elements.OutputNonce i e =
    Some (match nth_error (elements_nonces_of e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_nonces_of. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))) as [txo | ];
    cbn [option_map]; [destruct (txoNonce txo) as [[[odd w] | h] | ] | ]; reflexivity.
Qed.

Definition elements_output_nonces_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of elements_nonce_type elements_nonce_bytes 5 (elements_nonces_of e).

Theorem elements_output_nonces_hash_spec_sem e :
  @elements_output_nonces_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_output_nonces_hash_of e)).
Proof.
  unfold elements_output_nonces_hash_spec. cbv zeta.
  apply (hash_elems_reader_sem Elements.env elements_nonce_type
    (fun term => @elements_nonce_hash_spec term) elements_nonce_hash_spec_parametric
    elements_nonce_bytes elements_nonce_hash_option 5 _ e (elements_nonces_of e) 33).
  - intros i.
    change (@EFP.Combinators.prim _ _ elements_hash_alg Elements.OutputNonce i e =
      Some (match nth_error (elements_nonces_of e) (Z.to_nat (wz 5 i)) with
            Some x => inr x | None => inl tt end)).
    rewrite elements_hash_prim. apply elements_nonces_of_sem.
  - intro x. pose proof (elements_nonce_bytes_bound x). lia.
  - lia.
  - exact elems_bound_33.
Qed.

Theorem elements_output_nonces_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_output_nonces_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_output_nonces_hash_of 0 56 760)
    (fun a e => @elements_output_nonces_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _outputNoncesHash).
  - exact elements_output_nonces_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
