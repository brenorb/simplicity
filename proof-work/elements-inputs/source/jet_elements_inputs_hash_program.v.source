(** Original Elements inputs_hash getter against the literal composition of
    the already verified outpoints, sequences and annexes hash programs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_forWhile_seq.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_ctx8_spec C.jet_sha_finalize_spec.
Require Import C.jet_bitcoin_composite_hash C.jet_sha_hash_words_reader.
Require Import C.jet_elements_words_hash_program C.jet_elements_annexes_hash_program.
Require Import C.jet_elements_outpoints_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_inputs_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
          (@AC.pair _ _ _ core (@elements_input_outpoints_hash_spec alg)
            (@elements_prim_words_hash_spec 2 5 Elements.InputSequence alg)))
        (@ctx8_addn_spec 6 term))
      (@elements_input_annexes_hash_spec alg))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma elements_inputs_hash_spec_parametric : EFP.Parametric (@elements_inputs_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_input_outpoints_hash_spec_parametric alg1 alg2 R) as HO.
  pose proof (elements_input_annexes_hash_spec_parametric alg1 alg2 R) as HN.
  pose proof (elements_prim_words_hash_spec_parametric 2 5 Elements.InputSequence alg1 alg2 R) as HS.
  destruct R as [R [HA [HP]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_inputs_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|exact HN].
  apply (Alg.comp_Parametric RC); [|exact H6].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC); [exact HO|exact HS].
Qed.

Definition elements_inputs_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of
    (vector_values (Word 3) 6
       (from_hash256 (elements_input_outpoints_hash_of e),
        from_hash256 (elements_words_hash_of 2 5 (elements_input_sequences_words e))) ++
     vector_values (Word 3) 5 (from_hash256 (elements_input_annexes_hash_of e))).

Theorem elements_inputs_hash_spec_sem e :
  @elements_inputs_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_inputs_hash_of e)).
Proof.
  unfold elements_inputs_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env),
    (hr_pair Elements.env), (hr_pair Elements.env).
  rewrite (hr_core Elements.env (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite elements_input_outpoints_hash_spec_sem, elements_input_annexes_hash_spec_sem.
  rewrite (elements_prim_words_hash_spec_sem 2 5 Elements.InputSequence elements_input_sequences_words
    elements_input_sequences_words_sem elements_hash_words_bound_4).
  cbv beta iota.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)),
    (ctx8_addn_option 6).
  destruct (init_hash_sem
    (vector_values (Word 3) 6
       (from_hash256 (elements_input_outpoints_hash_of e),
        from_hash256 (elements_words_hash_of 2 5 (elements_input_sequences_words e))) ++
     vector_values (Word 3) 5 (from_hash256 (elements_input_annexes_hash_of e)))) as (cf & H1 & H2).
  { rewrite app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)),
    (ctx8_addn_option 5).
  use_add E2.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem elements_inputs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_inputs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_inputs_hash_of 0 440 760)
    (fun a e => @elements_inputs_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _inputsHash).
  - exact elements_inputs_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
