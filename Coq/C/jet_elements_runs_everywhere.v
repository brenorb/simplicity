(** Thirty Elements jets run and return the canonical result for EVERY logical
    environment and input: the environment relation of each contract is
    discharged by constructing a representing memory
    ([jet_elements_env_constructible], [jet_elements_elem_buildable]) and the
    frame premises by fresh frames (the executability theorems).  The
    statements mention no memory, frame or environment premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_uint32_array_init C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_application_contract C.jet_application_sep C.jet_frame_constructible_app.
Require Import C.jet_env_constructible C.jet_elements_prim C.jet_elements_linkage.
Require Import C.jet_elements_env_constructible C.jet_elements_elem_buildable.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets C.jet_elements_input_hash_jets.
Require Import C.jet_elements_output_proof_jets C.jet_elements_hash_elem.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_current_gen C.jet_elements_current_gen_jets.
Require Import C.jet_elements_executable C.jet_elements_executable_conf C.jet_elements_executable_current.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition runs_everywhere (f : function) (A B : Ty)
    (spec : A -> Elements.env -> option B) : Prop :=
  forall (a : A) (e : Elements.env),
  exists m bd bs bw env mf value,
    spec a e = Some value /\
    Clight2.eval_funcall elements_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode value).

Lemma sep_runs_everywhere f A B rep spec :
  application_sep_runs_on_fresh_frames f elements_ge Elements.env A B rep spec ->
  (forall e, exists m env fp, rep m env e fp /\ Forall (fun '(b, _, _) => Mem.valid_block m b) fp) ->
  runs_everywhere f A B spec.
Proof.
  intros HRun HRep a e. destruct (HRep e) as (m0 & env & fp & Hr & Hv).
  destruct (HRun a e env m0 fp Hr Hv) as (m & bd & bs & bw & mf & value & H1 & H2 & H3).
  exists m, bd, bs, bw, env, mf, value. repeat split; assumption.
Qed.

Ltac side e :=
  first [ lia | divides | exact Mem.empty
        | exact (proj1 (elements_inputs_fit e 544 ltac:(lia)))
        | exact (proj2 (elements_inputs_fit e 544 ltac:(lia)))
        | exact (proj1 (elements_outputs_fit e 248 ltac:(lia)))
        | exact (proj2 (elements_outputs_fit e 248 ltac:(lia)))
        | (left; lia) | (right; lia) ].

Ltac statement H :=
  lazymatch type of H with
  | application_sep_runs_on_fresh_frames ?f _ _ ?A ?B _ ?s => exact (runs_everywhere f A B s)
  end.

Theorem elements_input_amount_runs_everywhere :
  ltac:(statement elements_input_amount_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_input_amount_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\ amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi)))
      544 0 544 0 696 8);
    first [exact (asset_amount_local (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) 168 208 544 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          |exact (asset_amount_buildable (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) 168 208 544 ltac:(lia) ltac:(divides) ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_output_amount_runs_everywhere :
  ltac:(statement elements_output_amount_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_amount_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b (ofs + 0) (clearPrf (txoAsset txo)) /\ amount_rep m b (ofs + 104) (clearPrf (txoAmount txo)))
      248 0 248 8 704 8);
    first [exact (asset_amount_local (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) 0 104 248 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          |exact (asset_amount_buildable (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) 0 104 248 ltac:(lia) ltac:(divides) ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_input_asset_runs_everywhere :
  ltac:(statement elements_input_asset_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_input_asset_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi)))
      544 168 36 0 696 4);
    first [exact (asset_rep_local (fun txi => utxoAsset (sigTxiTxo txi)))
          |exact (asset_rep_buildable (fun txi => utxoAsset (sigTxiTxo txi)))
          |side e].
Qed.

Theorem elements_output_asset_runs_everywhere :
  ltac:(statement elements_output_asset_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_asset_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo)))
      248 0 36 8 704 4);
    first [exact (asset_rep_local (fun txo => clearPrf (txoAsset txo)))
          |exact (asset_rep_buildable (fun txo => clearPrf (txoAsset txo)))
          |side e].
Qed.

Theorem elements_output_nonce_runs_everywhere :
  ltac:(statement elements_output_nonce_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_nonce_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo))
      248 144 36 8 704 4);
    first [exact (nonce_rep_local txoNonce)
          |exact (nonce_rep_buildable txoNonce)
          |side e].
Qed.

Theorem elements_output_script_hash_runs_everywhere :
  ltac:(statement elements_output_script_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_script_hash_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (script_hash_words x))
      248 180 32 8 704 4);
    first [exact (words_local script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_input_prev_outpoint_runs_everywhere :
  ltac:(statement elements_input_prev_outpoint_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_input_prev_outpoint_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      outpoint_rep
      544 96 40 0 696 8);
    first [exact outpoint_rep_local
          |exact outpoint_rep_buildable
          |side e].
Qed.

Theorem elements_input_script_sig_hash_runs_everywhere :
  ltac:(statement elements_input_script_sig_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_input_script_sig_hash_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (script_sig_hash_words x))
      544 64 32 0 696 4);
    first [exact (words_local script_sig_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable script_sig_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_input_script_hash_runs_everywhere :
  ltac:(statement elements_input_script_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_input_script_hash_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (utxo_script_hash_words x))
      544 136 32 0 696 4);
    first [exact (words_local utxo_script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable utxo_script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_issuance_asset_proof_runs_everywhere :
  ltac:(statement elements_issuance_asset_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_issuance_asset_proof_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (issuance_asset_proof_words x))
      544 360 32 0 696 4);
    first [exact (words_local issuance_asset_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable issuance_asset_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_issuance_token_proof_runs_everywhere :
  ltac:(statement elements_issuance_token_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_issuance_token_proof_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (issuance_token_proof_words x))
      544 392 32 0 696 4);
    first [exact (words_local issuance_token_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable issuance_token_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_issuance_asset_amount_runs_everywhere :
  ltac:(statement elements_issuance_asset_amount_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_issuance_asset_amount_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      issuance_amount_rep
      544 256 280 0 696 8);
    first [exact issuance_amount_rep_local
          |exact issuance_amount_rep_buildable
          |side e].
Qed.

Theorem elements_reissuance_blinding_runs_everywhere :
  ltac:(statement elements_reissuance_blinding_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_reissuance_blinding_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 0 gh_blinding)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 0 gh_blinding ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 0 gh_blinding ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_new_issuance_contract_runs_everywhere :
  ltac:(statement elements_new_issuance_contract_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_new_issuance_contract_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 0 gh_contract)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 0 gh_contract ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 0 gh_contract ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_reissuance_entropy_runs_everywhere :
  ltac:(statement elements_reissuance_entropy_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_reissuance_entropy_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 72 gh_entropy)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 72 gh_entropy ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 72 gh_entropy ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_output_surjection_proof_runs_everywhere :
  ltac:(statement elements_output_surjection_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_surjection_proof_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (surjection_proof_hash_words x))
      248 36 32 8 704 4);
    first [exact (words_local surjection_proof_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable surjection_proof_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_output_range_proof_runs_everywhere :
  ltac:(statement elements_output_range_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_output_range_proof_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (range_proof_hash_words x))
      248 68 32 8 704 4);
    first [exact (words_local range_proof_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable range_proof_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_current_prev_outpoint_runs_everywhere :
  ltac:(statement elements_current_prev_outpoint_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_prev_outpoint_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      outpoint_rep
      544 96 40 0 696 8);
    first [exact outpoint_rep_local
          |exact outpoint_rep_buildable
          |side e].
Qed.

Theorem elements_current_asset_runs_everywhere :
  ltac:(statement elements_current_asset_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_asset_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi)))
      544 168 36 0 696 4);
    first [exact (asset_rep_local (fun txi => utxoAsset (sigTxiTxo txi)))
          |exact (asset_rep_buildable (fun txi => utxoAsset (sigTxiTxo txi)))
          |side e].
Qed.

Theorem elements_current_script_hash_runs_everywhere :
  ltac:(statement elements_current_script_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_script_hash_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (utxo_script_hash_words x))
      544 136 32 0 696 4);
    first [exact (words_local utxo_script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable utxo_script_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_current_script_sig_hash_runs_everywhere :
  ltac:(statement elements_current_script_sig_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_script_sig_hash_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (script_sig_hash_words x))
      544 64 32 0 696 4);
    first [exact (words_local script_sig_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable script_sig_hash_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_current_issuance_asset_proof_runs_everywhere :
  ltac:(statement elements_current_issuance_asset_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_issuance_asset_proof_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (issuance_asset_proof_words x))
      544 360 32 0 696 4);
    first [exact (words_local issuance_asset_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable issuance_asset_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_current_issuance_token_proof_runs_everywhere :
  ltac:(statement elements_current_issuance_token_proof_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_issuance_token_proof_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs x => uint32_array_at m b ofs (issuance_token_proof_words x))
      544 392 32 0 696 4);
    first [exact (words_local issuance_token_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |exact (words_buildable issuance_token_proof_words ltac:(intro; exact (Digest.hash256_len _)))
          |side e].
Qed.

Theorem elements_current_reissuance_blinding_runs_everywhere :
  ltac:(statement elements_current_reissuance_blinding_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_reissuance_blinding_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 0 gh_blinding)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 0 gh_blinding ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 0 gh_blinding ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_current_new_issuance_contract_runs_everywhere :
  ltac:(statement elements_current_new_issuance_contract_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_new_issuance_contract_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 0 gh_contract)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 0 gh_contract ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 0 gh_contract ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_current_reissuance_entropy_runs_everywhere :
  ltac:(statement elements_current_reissuance_entropy_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_reissuance_entropy_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (issuance_hash_rep 72 gh_entropy)
      544 256 280 0 696 8);
    first [exact (issuance_hash_rep_local 72 gh_entropy ltac:(lia) ltac:(lia))
          |exact (issuance_hash_rep_buildable 72 gh_entropy ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_current_issuance_asset_amount_runs_everywhere :
  ltac:(statement elements_current_issuance_asset_amount_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_issuance_asset_amount_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      issuance_amount_rep
      544 256 280 0 696 8);
    first [exact issuance_amount_rep_local
          |exact issuance_amount_rep_buildable
          |side e].
Qed.

Theorem elements_current_amount_runs_everywhere :
  ltac:(statement elements_current_amount_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_amount_local_spec_executable|].
  intros e.
  eapply (@current_gen_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      input_amount_elem_rep
      544 0 696);
    first [exact (asset_amount_local (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) 168 208 544 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          |exact (asset_amount_buildable (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) 168 208 544 ltac:(lia) ltac:(divides) ltac:(lia) ltac:(divides) ltac:(lia))
          |side e].
Qed.

Theorem elements_current_pegin_runs_everywhere :
  ltac:(statement elements_current_pegin_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_pegin_local_spec_executable|].
  intros e.
  eapply (@current_gen_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (flag_hash_rep sigTxiPegin 537 32)
      544 0 696);
    first [exact (flag_hash_rep_local sigTxiPegin 537 32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          |exact (flag_hash_rep_buildable sigTxiPegin 537 32 ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia))
          |side e].
Qed.

Theorem elements_current_annex_hash_runs_everywhere :
  ltac:(statement elements_current_annex_hash_local_spec_executable).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_annex_hash_local_spec_executable|].
  intros e.
  eapply (@current_gen_rep_constructible _ (fun e => sigTxIn (Elements.envTx e))
      (flag_hash_rep annex_hash_of 536 0)
      544 0 696);
    first [exact (flag_hash_rep_local annex_hash_of 536 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          |exact (flag_hash_rep_buildable annex_hash_of 536 0 ltac:(lia) ltac:(divides) ltac:(lia) ltac:(lia))
          |side e].
Qed.
