(** Original Elements outputs_hash and input_utxos_hash C getters against
    the canonical compositions of their primitive-based hash programs. *)
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
Require Import C.jet_elements_words_hash_program C.jet_elements_nonces_hash_program.
Require Import C.jet_elements_amounts_hash_program.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_fixed_vector_hash_spec (k : nat) {alg : EFP.Algebra}
    (payload : EFP.domain alg Ty.Unit (Vector Word8 k)) : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core) payload)
    (@AC.comp _ _ _ core (@ctx8_addn_spec k term) (@ctx8_finalize_spec term)).

Lemma elements_fixed_vector_hash_spec_parametric k
    (payload : forall alg : EFP.Algebra, EFP.domain alg Ty.Unit (Vector Word8 k)) :
  EFP.Parametric payload ->
  EFP.Parametric (fun alg => @elements_fixed_vector_hash_spec k alg (payload alg)).
Proof.
  intros HP alg1 alg2 R. specialize (HP alg1 alg2 R).
  destruct R as [R [HA [HPrim]]]. set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric k _ _ RA) as HK.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_fixed_vector_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact HK|exact HF]].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|exact HP].
Qed.

Lemma elements_fixed_vector_hash_spec_sem k
    (payload : EFP.domain elements_hash_alg Ty.Unit (Vector Word8 k)) x e :
  payload tt e = Some x ->
  Z.of_nat (Nat.pow 2 k) / 64 < ctx8_limit ->
  @elements_fixed_vector_hash_spec k elements_hash_alg payload tt e =
    Some (from_hash256 (sha256_bytes_of (vector_values Word8 k x))).
Proof.
  intros HP HB. unfold elements_fixed_vector_hash_spec. cbv zeta.
  rewrite (hr_comp Elements.env), (hr_pair Elements.env), HP.
  rewrite (hr_core Elements.env (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  cbv beta iota. rewrite (hr_comp Elements.env).
  rewrite (hr_assert Elements.env (fun alg => @ctx8_addn_spec k alg) (ctx8_addn_spec_parametric k)),
    (ctx8_addn_option k).
  destruct (init_hash_sem (vector_values Word8 k x)) as (cf & HAdd & HFin).
  { rewrite vector_values_length. exact HB. }
  use_add HAdd.
  rewrite (hr_assert Elements.env (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact HFin.
Qed.

Definition elements_outputs_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @elements_fixed_vector_hash_spec 7 alg
    (@AC.pair _ _ _ core
      (@AC.pair _ _ _ core (@elements_output_amounts_hash_spec alg) (@elements_output_nonces_hash_spec alg))
      (@AC.pair _ _ _ core (@elements_prim_words_hash_spec 5 5 Elements.OutputScriptHash alg)
        (@elements_prim_words_hash_spec 5 5 Elements.OutputRangeProof alg))).

Lemma elements_outputs_hash_spec_parametric : EFP.Parametric (@elements_outputs_hash_spec).
Proof.
  unfold elements_outputs_hash_spec. cbv zeta.
  apply elements_fixed_vector_hash_spec_parametric.
  intros alg1 alg2 R.
  pose proof (elements_amounts_hash_spec_parametric Elements.OutputAmount Elements.OutputAsset alg1 alg2 R) as HA.
  pose proof (elements_output_nonces_hash_spec_parametric alg1 alg2 R) as HN.
  pose proof (elements_prim_words_hash_spec_parametric 5 5 Elements.OutputScriptHash alg1 alg2 R) as HS.
  pose proof (elements_prim_words_hash_spec_parametric 5 5 Elements.OutputRangeProof alg1 alg2 R) as HR.
  destruct R as [R [[HC HAm] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.pair_Parametric RC); apply (Alg.pair_Parametric RC); assumption.
Qed.

Definition elements_outputs_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of (vector_values Word8 7
    ((from_hash256 (elements_output_amounts_hash_of e), from_hash256 (elements_output_nonces_hash_of e)),
     (from_hash256 (elements_words_hash_of 5 5 (elements_output_scripts_words e)),
      from_hash256 (elements_words_hash_of 5 5 (elements_output_range_proofs_words e))))).

Theorem elements_outputs_hash_spec_sem e :
  @elements_outputs_hash_spec elements_hash_alg tt e = Some (from_hash256 (elements_outputs_hash_of e)).
Proof.
  unfold elements_outputs_hash_spec, elements_outputs_hash_of. cbv zeta.
  apply elements_fixed_vector_hash_spec_sem.
  - rewrite !(hr_pair Elements.env).
    rewrite (elements_amounts_hash_spec_sem Elements.OutputAmount Elements.OutputAsset
      elements_output_amounts_of elements_output_amounts_of_sem).
    rewrite elements_output_nonces_hash_spec_sem.
    rewrite (elements_prim_words_hash_spec_sem 5 5 Elements.OutputScriptHash elements_output_scripts_words
      elements_output_scripts_words_sem elements_hash_words_bound_32).
    rewrite (elements_prim_words_hash_spec_sem 5 5 Elements.OutputRangeProof elements_output_range_proofs_words
      elements_output_range_proofs_words_sem elements_hash_words_bound_32).
    reflexivity.
  - vm_compute; reflexivity.
Qed.

Theorem elements_outputs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_outputs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_outputs_hash_of 0 184 760)
    (fun a e => @elements_outputs_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _outputsHash).
  - exact elements_outputs_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.

Definition elements_input_utxos_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let core := Alg.Assertion.toCore (EFP.CanonicalStructures.toAssertion alg) in
  @elements_fixed_vector_hash_spec 6 alg
    (@AC.pair _ _ _ core (@elements_input_amounts_hash_spec alg)
      (@elements_prim_words_hash_spec 5 5 Elements.InputScriptHash alg)).

Lemma elements_input_utxos_hash_spec_parametric : EFP.Parametric (@elements_input_utxos_hash_spec).
Proof.
  unfold elements_input_utxos_hash_spec. cbv zeta.
  apply elements_fixed_vector_hash_spec_parametric.
  intros alg1 alg2 R.
  pose proof (elements_amounts_hash_spec_parametric Elements.InputAmount Elements.InputAsset alg1 alg2 R) as HA.
  pose proof (elements_prim_words_hash_spec_parametric 5 5 Elements.InputScriptHash alg1 alg2 R) as HS.
  destruct R as [R [[HC HAm] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.pair_Parametric RC); assumption.
Qed.

Definition elements_input_utxos_hash_of (e : Elements.env) : hash256 :=
  sha256_bytes_of (vector_values Word8 6
    (from_hash256 (elements_input_amounts_hash_of e),
     from_hash256 (elements_words_hash_of 5 5 (elements_input_scripts_words e)))).

Theorem elements_input_utxos_hash_spec_sem e :
  @elements_input_utxos_hash_spec elements_hash_alg tt e =
    Some (from_hash256 (elements_input_utxos_hash_of e)).
Proof.
  unfold elements_input_utxos_hash_spec, elements_input_utxos_hash_of. cbv zeta.
  apply elements_fixed_vector_hash_spec_sem.
  - rewrite (hr_pair Elements.env).
    rewrite (elements_amounts_hash_spec_sem Elements.InputAmount Elements.InputAsset
      elements_input_amounts_of elements_input_amounts_of_sem).
    rewrite (elements_prim_words_hash_spec_sem 5 5 Elements.InputScriptHash elements_input_scripts_words
      elements_input_scripts_words_sem elements_hash_words_bound_32).
    reflexivity.
  - vm_compute; reflexivity.
Qed.

Theorem elements_input_utxos_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_utxos_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep elements_input_utxos_hash_of 0 312 760)
    (fun a e => @elements_input_utxos_hash_spec elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _inputUTXOsHash).
  - exact elements_input_utxos_hash_spec_sem.
  - elements_hash_getter_shape.
  - exact elements_txEnv_tx.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
