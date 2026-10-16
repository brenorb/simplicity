(** Original Elements C cache getters against their literal Simplicity
    hash-word programs, interpreted with primitives over raw Elements data.
    Cache/frame representation remains an explicit caller obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Primitive Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Require Import C.jet_elements_hash_getter_local C.jet_elements_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_forWhile_seq C.jet_sha_ctx8_spec.
Require Import C.jet_sha_hash_words C.jet_sha_hash_words_reader.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Module EFP := PrimitiveElements.Primitive.
Notation elements_hash_alg := (EFP.Theory.PrimitivePrimSem option_Monad_Zero).
Local Notation ea := (EFP.CanonicalStructures.toAssertion elements_hash_alg).
Local Notation ec := (Alg.Assertion.toCore ea).

Lemma elements_hash_prim {A B : Ty} (p : Elements.t A B) a e :
  @EFP.Combinators.prim A B elements_hash_alg p a e = Elements.sem p a e.
Proof. cbv -[Elements.sem]. destruct (Elements.sem p a e); reflexivity. Qed.

Definition elements_prim_words_hash_spec (k w : nat)
    (p : Elements.t (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k))) {alg : EFP.Algebra} :
    EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_words_spec k w term Ty.Unit
    (@AC.drop Ty.Unit (Word w) _ core (@EFP.Combinators.prim _ _ alg p)).

Lemma elements_prim_words_hash_spec_parametric k w p :
  EFP.Parametric (@elements_prim_words_hash_spec k w p).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold elements_prim_words_hash_spec. cbv zeta.
  apply (hash_words_spec_parametric k w RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). apply HP.
Qed.

Definition elements_words_hash_of (k w : nat)
    (xs : list (Ty.tySem (Vector (Word 3) k))) : hash256 :=
  hash_words_of k (firstn (Z.to_nat (wsize w)) xs).

Theorem elements_prim_words_hash_spec_sem k w p
    (xs_of : Elements.env -> list (Ty.tySem (Vector (Word 3) k))) :
  (forall i e, @Elements.sem (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  forall e, @elements_prim_words_hash_spec k w p elements_hash_alg tt e =
    Some (from_hash256 (elements_words_hash_of k w (xs_of e))).
Proof.
  intros Hsem HB e. unfold elements_prim_words_hash_spec. cbv zeta.
  apply (hash_words_reader_sem Elements.env k w Ty.Unit _ tt e (xs_of e)); [ | exact HB].
  intros i.
  change (@EFP.Combinators.prim _ _ elements_hash_alg p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)).
  rewrite elements_hash_prim. apply Hsem.
Qed.

Theorem elements_tx_words_hash_jet k w p xs_of (f : function) (field : ident) (hdelta : Z) :
  (forall i e, @Elements.sem (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  elements_wrapper_shape f (elements_simple_rest (elements_hash_mid_writeHash _tx _elementsTransaction field)) ->
  elements_field_at _elementsTransaction field hdelta ->
  0 <= hdelta /\ hdelta + 32 <= 760 ->
  application_jet_local_spec_sep f elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of k w (xs_of e)) 0 hdelta 760)
    (fun a e => @elements_prim_words_hash_spec k w p elements_hash_alg a e).
Proof.
  intros HS HB HShape HField HRange.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := field).
  - exact (elements_prim_words_hash_spec_sem k w p xs_of HS HB).
  - exact HShape.
  - exact elements_txEnv_tx.
  - exact HField.
  - lia.
  - exact HRange.
Qed.

Lemma elements_hash_words_bound_32 : Z.of_nat (Nat.pow 2 5) * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.
Lemma elements_hash_words_bound_4 : Z.of_nat (Nat.pow 2 2) * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.
Lemma elements_hash_words_bound_path : Z.of_nat (Nat.pow 2 5) * wsize 3 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Ltac elements_hash_getter_shape :=
  repeat split; try reflexivity;
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with Hchoice : _ \/ _ |- _ => destruct Hchoice end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

Definition elements_output_scripts_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun o => from_hash256 (byteStringHash (txoScript o))) (sigTxOut (Elements.envTx e)).
Lemma elements_output_scripts_words_sem i e :
  Elements.sem Elements.OutputScriptHash i e =
    Some (match nth_error (elements_output_scripts_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_output_scripts_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_output_scripts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_output_scripts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_scripts_words e)) 0 88 760)
    (fun a e => @elements_prim_words_hash_spec 5 5 Elements.OutputScriptHash elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _outputScriptsHash).
  - exact elements_output_scripts_words_sem.
  - exact elements_hash_words_bound_32.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_output_range_proofs_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun o => from_hash256 (byteStringHash (viewPrf (txoAmount o)))) (sigTxOut (Elements.envTx e)).
Lemma elements_output_range_proofs_words_sem i e :
  Elements.sem Elements.OutputRangeProof i e =
    Some (match nth_error (elements_output_range_proofs_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_output_range_proofs_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_output_range_proofs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_output_range_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_range_proofs_words e)) 0 120 760)
    (fun a e => @elements_prim_words_hash_spec 5 5 Elements.OutputRangeProof elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _outputRangeProofsHash).
  - exact elements_output_range_proofs_words_sem.
  - exact elements_hash_words_bound_32.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_output_surjection_proofs_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun o => from_hash256 (byteStringHash (viewPrf (txoAsset o)))) (sigTxOut (Elements.envTx e)).
Lemma elements_output_surjection_proofs_words_sem i e :
  Elements.sem Elements.OutputSurjectionProof i e =
    Some (match nth_error (elements_output_surjection_proofs_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_output_surjection_proofs_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxOut (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_output_surjection_proofs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_output_surjection_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_surjection_proofs_words e)) 0 152 760)
    (fun a e => @elements_prim_words_hash_spec 5 5 Elements.OutputSurjectionProof elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _outputSurjectionProofsHash).
  - exact elements_output_surjection_proofs_words_sem.
  - exact elements_hash_words_bound_32.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_input_scripts_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun i => from_hash256 (byteStringHash (utxoScript (sigTxiTxo i)))) (sigTxIn (Elements.envTx e)).
Lemma elements_input_scripts_words_sem i e :
  Elements.sem Elements.InputScriptHash i e =
    Some (match nth_error (elements_input_scripts_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_input_scripts_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_input_scripts_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_scripts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_input_scripts_words e)) 0 280 760)
    (fun a e => @elements_prim_words_hash_spec 5 5 Elements.InputScriptHash elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _inputScriptsHash).
  - exact elements_input_scripts_words_sem.
  - exact elements_hash_words_bound_32.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_input_sequences_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 2)) :=
  map (fun i => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence i))) (sigTxIn (Elements.envTx e)).
Lemma elements_input_sequences_words_sem i e :
  Elements.sem Elements.InputSequence i e =
    Some (match nth_error (elements_input_sequences_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_input_sequences_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_input_sequences_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_sequences_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 2 5 (elements_input_sequences_words e)) 0 344 760)
    (fun a e => @elements_prim_words_hash_spec 2 5 Elements.InputSequence elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _inputSequencesHash).
  - exact elements_input_sequences_words_sem.
  - exact elements_hash_words_bound_4.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_input_script_sigs_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun i => from_hash256 (byteStringHash (sigTxiScriptSig i))) (sigTxIn (Elements.envTx e)).
Lemma elements_input_script_sigs_words_sem i e :
  Elements.sem Elements.InputScriptSigHash i e =
    Some (match nth_error (elements_input_script_sigs_words e) (Z.to_nat (wz 5 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_input_script_sigs_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_input_script_sigs_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_input_script_sigs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_input_script_sigs_words e)) 0 408 760)
    (fun a e => @elements_prim_words_hash_spec 5 5 Elements.InputScriptSigHash elements_hash_alg a e).
Proof.
  eapply elements_tx_words_hash_jet with (field := _inputScriptSigsHash).
  - exact elements_input_script_sigs_words_sem.
  - exact elements_hash_words_bound_32.
  - elements_hash_getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

Definition elements_tappath_words (e : Elements.env) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map from_hash256 (tappath (Elements.envTap e)).
Lemma elements_tappath_words_sem i e :
  Elements.sem Elements.Tappath i e =
    Some (match nth_error (elements_tappath_words e) (Z.to_nat (wz 3 i)) with
          Some x => inr x | None => inl tt end).
Proof.
  unfold elements_tappath_words. rewrite nth_error_map. unfold wz, Elements.sem.
  destruct (nth_error (tappath (Elements.envTap e)) (Z.to_nat (toZ i))); reflexivity.
Qed.

Theorem elements_tappath_hash_program_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 3 (elements_tappath_words e)) 8 40 176)
    (fun a e => @elements_prim_words_hash_spec 5 3 Elements.Tappath elements_hash_alg a e).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _elementsTapEnv)
    (hashfield := _tappathHash).
  - exact (elements_prim_words_hash_spec_sem 5 3 Elements.Tappath elements_tappath_words
      elements_tappath_words_sem elements_hash_words_bound_path).
  - elements_hash_getter_shape.
  - exact elements_txEnv_taproot.
  - vm_compute; reflexivity.
  - lia.
  - lia.
Qed.
