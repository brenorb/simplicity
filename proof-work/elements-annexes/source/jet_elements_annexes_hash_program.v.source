(** The original Elements input_annexes_hash C jet against the literal
    primitive/annexHash loop.  The cache/frame relation is explicit, not an
    assumed execution or a new cached-hash primitive. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_forWhile_seq C.jet_sha_ctx8_spec.
Require Import C.jet_bitcoin_ctx_hash_spec C.jet_sha_hash_loop_gen C.jet_bitcoin_tx_hash.
Require Import C.jet_sha_hash_words_reader C.jet_sha_hash_elems_reader.
Require Import C.jet_elements_words_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_input_annexes_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_elems_spec (Ty.Sum Ty.Unit Word256) (fun term => @annex_hash_spec term) 5 term
    (@AC.drop Ty.Unit Word32 _ core (@EFP.Combinators.prim _ _ alg Elements.InputAnnexHash)).

Lemma elements_input_annexes_hash_spec_parametric : EFP.Parametric (@elements_input_annexes_hash_spec).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_input_annexes_hash_spec. cbv zeta.
  apply (hash_elems_spec_parametric _ _ annex_hash_spec_parametric 5 RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). apply HP.
Qed.

Definition elements_annexes_of (e : Elements.env) : list (Ty.tySem (Ty.Sum Ty.Unit Word256)) :=
  map (fun txi => match sigTxiAnnex txi with
                   | None => inl tt
                   | Some bs => inr (from_hash256 (byteStringHash bs))
                   end) (sigTxIn (Elements.envTx e)).

Lemma elements_annexes_of_sem i e :
  Elements.sem Elements.InputAnnexHash i e =
    Some (match nth_error (elements_annexes_of e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_annexes_of. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))) as [txi | ]; cbn [option_map];
    [destruct (sigTxiAnnex txi) | ]; reflexivity.
Qed.

Definition elements_input_annexes_hash_of (e : Elements.env) : hash256 :=
  elems_hash_of (Ty.Sum Ty.Unit Word256) annex_elem_bytes 5 (elements_annexes_of e).

Theorem elements_input_annexes_hash_spec_sem e :
  @elements_input_annexes_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_input_annexes_hash_of e)).
Proof.
  unfold elements_input_annexes_hash_spec. cbv zeta.
  apply (hash_elems_reader_sem Elements.env (Ty.Sum Ty.Unit Word256)
    (fun term => @annex_hash_spec term) annex_hash_spec_parametric annex_elem_bytes annex_add_option
    5 _ e (elements_annexes_of e) 33).
  - intros i.
    change (@EFP.Combinators.prim _ _ elements_hash_alg Elements.InputAnnexHash i e =
      Some (match nth_error (elements_annexes_of e) (Z.to_nat (wz 5 i)) with
            Some x => inr x | None => inl tt end)).
    rewrite elements_hash_prim. apply elements_annexes_of_sem.
  - exact annex_bytes_bound.
  - lia.
  - exact elems_bound_33.
Qed.

Theorem elements_input_annexes_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_annexes_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_annexes_hash_of 0 376 760)
    (fun a e => @elements_input_annexes_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _inputAnnexesHash).
  - exact elements_input_annexes_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
