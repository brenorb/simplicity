(** The complete canonical Elements txHash program and the original C getter.
    Reuse the component programs and the shared list-absorption proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_bitcoin_composite_hash.
Require Import C.jet_elements_words_hash_program C.jet_sha_hash_words_reader.
Require Import C.jet_elements_inputs_hash_program C.jet_elements_inputs_hash_literal.
Require Import C.jet_elements_composite_amounts_hash C.jet_elements_composite_hash_literal.
Require Import C.jet_elements_issuances_hash_literal C.jet_elements_array_hash_literal.
Require Import C.jet_sha_ctx8_literal C.jet_sha_finalize_literal C.jet_sha_hash_words_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_tx_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
              (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.Version)
                (@EFP.Combinators.prim _ _ alg Elements.LockTime)))
            (@ctx8_addn_spec 3 term))
          (@AC.pair _ _ _ core
            (@AC.pair _ _ _ core (@elements_inputs_hash_spec alg) (@elements_outputs_hash_spec alg))
            (@AC.pair _ _ _ core (@elements_issuances_hash_spec alg)
              (@elements_prim_words_hash_spec 5 5 Elements.OutputSurjectionProof alg))))
        (@ctx8_addn_spec 7 term))
      (@elements_input_utxos_hash_spec alg))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).

Lemma elements_tx_hash_spec_parametric : EFP.Parametric (@elements_tx_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (elements_inputs_hash_spec_parametric alg1 alg2 R) as HI.
  pose proof (elements_outputs_hash_spec_parametric alg1 alg2 R) as HO.
  pose proof (elements_issuances_hash_spec_parametric alg1 alg2 R) as HIs.
  pose proof (elements_prim_words_hash_spec_parametric 5 5 Elements.OutputSurjectionProof alg1 alg2 R) as HS.
  pose proof (elements_input_utxos_hash_spec_parametric alg1 alg2 R) as HU.
  destruct R as [R [HA [HP]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 3 _ _ RA) as H3.
  pose proof (ctx8_addn_spec_parametric 5 _ _ RA) as H5.
  pose proof (ctx8_addn_spec_parametric 7 _ _ RA) as H7.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_tx_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H5|exact HF]].
  apply (Alg.pair_Parametric RC); [|exact HU].
  apply (Alg.comp_Parametric RC); [|exact H7].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [|exact H3].
    apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
    apply (Alg.pair_Parametric RC); apply HP.
  - apply (Alg.pair_Parametric RC); apply (Alg.pair_Parametric RC); assumption.
Qed.

Definition elements_tx_version_word (e : Elements.env) : Ty.tySem Word32 :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxVersion (Elements.envTx e))).
Definition elements_tx_locktime_word (e : Elements.env) : Ty.tySem Word32 :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxLock (Elements.envTx e))).

Definition elements_tx_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of
    (vector_values Word8 3 (elements_tx_version_word e, elements_tx_locktime_word e) ++
     vector_values Word8 7
       ((from_hash256 (elements_inputs_hash_of e), from_hash256 (elements_outputs_hash_of e)),
        (from_hash256 (elements_issuances_hash_of e),
         from_hash256 (elements_words_hash_of 5 5 (elements_output_surjection_proofs_words e)))) ++
     vector_values Word8 5 (from_hash256 (elements_input_utxos_hash_of e))).

Theorem elements_tx_hash_spec_sem e :
  @elements_tx_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_tx_hash_of e)).
Proof.
  unfold elements_tx_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), (hr_comp Elements.env),
    (hr_pair Elements.env), (hr_comp Elements.env), (hr_pair Elements.env),
    (hr_pair Elements.env), (hr_pair Elements.env), (hr_pair Elements.env), (hr_pair Elements.env).
  rewrite (hr_core Elements.env (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite !elements_hash_prim.
  change (Elements.sem Elements.Version tt e) with (Some (elements_tx_version_word e)).
  change (Elements.sem Elements.LockTime tt e) with (Some (elements_tx_locktime_word e)).
  rewrite elements_inputs_hash_spec_sem, elements_outputs_hash_spec_sem,
    elements_issuances_hash_spec_sem, elements_input_utxos_hash_spec_sem.
  rewrite (elements_prim_words_hash_spec_sem 5 5 Elements.OutputSurjectionProof
    elements_output_surjection_proofs_words elements_output_surjection_proofs_words_sem elements_hash_words_bound_32).
  cbv beta iota.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 3 alg) (ctx8_addn_spec_parametric 3)), (ctx8_addn_option 3).
  destruct (init_hash_sem
    (vector_values Word8 3 (elements_tx_version_word e, elements_tx_locktime_word e) ++
     vector_values Word8 7
       ((from_hash256 (elements_inputs_hash_of e), from_hash256 (elements_outputs_hash_of e)),
        (from_hash256 (elements_issuances_hash_of e),
         from_hash256 (elements_words_hash_of 5 5 (elements_output_surjection_proofs_words e)))) ++
     vector_values Word8 5 (from_hash256 (elements_input_utxos_hash_of e)))) as (cf & H1 & H2).
  { rewrite !app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  destruct (add_app_some _ _ _ _ E2) as (c2 & E3 & E4).
  use_add E1. cbv beta iota.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 7 alg) (ctx8_addn_spec_parametric 7)), (ctx8_addn_option 7).
  use_add E3. cbv beta iota. rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec 5 alg) (ctx8_addn_spec_parametric 5)), (ctx8_addn_option 5).
  use_add E4.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem elements_tx_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_tx_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_tx_hash_of 0 632 760)
    (fun a e => @elements_tx_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _txHash).
  - exact elements_tx_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

Definition literal_elements_tx_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core
          (@AC.comp _ _ _ core
            (@AC.pair _ _ _ core (@literal_sha_hash_ctx_init core)
              (@AC.pair _ _ _ core (@EFP.Combinators.prim _ _ alg Elements.Version)
                (@EFP.Combinators.prim _ _ alg Elements.LockTime)))
            (@literal_ctx8_addn 3 term))
          (@AC.pair _ _ _ core
            (@AC.pair _ _ _ core (@literal_elements_inputs_hash alg) (@literal_elements_outputs_hash alg))
            (@AC.pair _ _ _ core (@literal_elements_issuances_hash alg)
              (@literal_elements_output_surjection_proofs_hash alg))))
        (@literal_ctx8_addn 7 term))
      (@literal_elements_input_utxos_hash alg))
    (@AC.comp _ _ _ core (@literal_ctx8_addn 5 term) (@literal_ctx8_finalize term)).

Lemma literal_elements_tx_hash_matches alg : @literal_elements_tx_hash alg = @elements_tx_hash_spec alg.
Proof.
  unfold literal_elements_tx_hash, elements_tx_hash_spec.
  rewrite (literal_elements_inputs_hash_matches alg), (literal_elements_outputs_hash_matches alg),
    (literal_elements_issuances_hash_matches alg), (literal_elements_input_utxos_hash_matches alg).
  unfold literal_elements_output_surjection_proofs_hash.
  rewrite literal_elements_array_hash_matches, literal_sha_hash_ctx_init_matches,
    !literal_ctx8_addn_algebra_matches, literal_ctx8_finalize_algebra_matches. reflexivity.
Qed.

Lemma literal_elements_tx_hash_parametric : EFP.Parametric (@literal_elements_tx_hash).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_tx_hash_matches alg1), (literal_elements_tx_hash_matches alg2).
  exact (elements_tx_hash_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_tx_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tx_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_tx_hash_of 0 632 760)
    (fun a environment => @literal_elements_tx_hash elements_hash_alg a environment).
Proof. rewrite literal_elements_tx_hash_matches. exact elements_tx_hash_program_local_spec. Qed.
