(** The SigHash programs of the shape [hashWords (drop (primitive P))]:
    outputValuesHash, outputScriptsHash, inputValuesHash, inputScriptsHash,
    inputSequencesHash, inputScriptSigsHash and tappathHash, with their
    values, and the C getters that return the cached hashes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_forWhile_seq.
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 120.

Definition prim_words_hash_spec (k w : nat)
    (p : BitcoinFull.t (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k))) {alg : PF.Algebra} :
    PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @hash_words_spec k w term Ty.Unit
    (@AC.drop Ty.Unit (Word w) _ core (@PF.Combinators.prim _ _ alg p)).

Lemma prim_words_hash_spec_parametric k w p : PF.Parametric (@prim_words_hash_spec k w p).
Proof.
  intros alg1 alg2 R. destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  unfold prim_words_hash_spec. cbv zeta.
  apply (hash_words_spec_parametric k w RA).
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.drop_Parametric RC). apply HP.
Qed.

Definition words_hash_of (k w : nat) (xs : list (Ty.tySem (Vector (Word 3) k))) : hash256 :=
  hash_words_of k (firstn (Z.to_nat (wsize w)) xs).

Theorem prim_words_hash_spec_sem k w p (xs_of : ext_environment -> list (Ty.tySem (Vector (Word 3) k))) :
  (forall i e, @BitcoinFull.sem (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  forall e, @prim_words_hash_spec k w p fullalg tt e = Some (from_hash256 (words_hash_of k w (xs_of e))).
Proof.
  intros Hsem HB e. unfold prim_words_hash_spec. cbv zeta.
  apply (hash_words_sem k w Ty.Unit _ tt e (xs_of e)); [|exact HB].
  intros i. rewrite fx_drop. cbn [snd]. rewrite fx_prim. apply Hsem.
Qed.

(** The getters of a hash cached in the transaction. *)
Theorem tx_words_hash_jet k w p xs_of (f : function) (field : ident) (hdelta : Z) :
  (forall i e, @BitcoinFull.sem (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_hash_mid_writeHash _tx _bitcoinTransaction field)) ->
  bitcoin_field_at _bitcoinTransaction field hdelta ->
  0 <= hdelta /\ hdelta + 32 <= 432 ->
  application_jet_local_spec_sep f bitcoin_ge ext_environment Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of k w (xs_of e)) 0 hdelta 432)
    (fun a environment => @prim_words_hash_spec k w p fullalg a environment).
Proof.
  intros Hsem HB Hshape Hfield Hh.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _tx) (sid := _bitcoinTransaction)
    (hashfield := field).
  - intros e. apply (prim_words_hash_spec_sem k w p xs_of Hsem HB).
  - exact Hshape.
  - exact bitcoin_txEnv_tx.
  - exact Hfield.
  - lia.
  - exact Hh.
Qed.

Lemma words_bound_8 : Z.of_nat (Nat.pow 2 3) * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.
Lemma words_bound_32 : Z.of_nat (Nat.pow 2 5) * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.
Lemma words_bound_4 : Z.of_nat (Nat.pow 2 2) * wsize 5 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

Ltac getter_shape :=
  repeat split; try reflexivity;
  let x := fresh in let y := fresh in let HX := fresh in let HY := fresh in let Hxy := fresh in
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

(** ** outputValuesHash = hashWord64s (drop (primitive OutputValue)) *)
Definition output_values_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 3)) :=
  map (fun o => @fromZ (WordToZ 6) (Int64.signed (txoValue o)))
    (sigTxOut (Bitcoin.envTx (extBase e))).

Lemma output_values_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 3)) (BitcoinFull.Base Bitcoin.OutputValue) i e =
    Some (match nth_error (output_values_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold output_values_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem.
  destruct (nth_error (sigTxOut (Bitcoin.envTx (extBase e))) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_output_values_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_values_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 3 5 (output_values_of e)) 0 16 432)
    (fun a environment =>
      @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.OutputValue) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 3 5 (BitcoinFull.Base Bitcoin.OutputValue) output_values_of
    f_simplicity_bitcoin_output_values_hash _outputValuesHash 16 output_values_sem words_bound_8).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** ** outputScriptsHash = hashWord256s32 (drop (primitive OutputScriptHash)) *)
Definition output_scripts_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun x => from_hash256 (byteStringHash (txoScript x))) (sigTxOut (Bitcoin.envTx (extBase e))).

Lemma output_scripts_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 5)) (BitcoinFull.Base Bitcoin.OutputScriptHash) i e =
    Some (match nth_error (output_scripts_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold output_scripts_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (sigTxOut (Bitcoin.envTx (extBase e))) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_output_scripts_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_scripts_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (output_scripts_of e)) 0 48 432)
    (fun a environment =>
      @prim_words_hash_spec 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 5 5 (BitcoinFull.Base Bitcoin.OutputScriptHash) output_scripts_of
    f_simplicity_bitcoin_output_scripts_hash _outputScriptsHash 48 output_scripts_sem words_bound_32).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** ** inputValuesHash = hashWord64s (drop (primitive InputValue)) *)
Definition input_values_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 3)) :=
  map (fun x => @fromZ (WordToZ 6) (Int64.signed (sigTxiValue x))) (sigTxIn (Bitcoin.envTx (extBase e))).

Lemma input_values_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 3)) (BitcoinFull.Base Bitcoin.InputValue) i e =
    Some (match nth_error (input_values_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold input_values_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (sigTxIn (Bitcoin.envTx (extBase e))) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_input_values_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_values_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 3 5 (input_values_of e)) 0 144 432)
    (fun a environment =>
      @prim_words_hash_spec 3 5 (BitcoinFull.Base Bitcoin.InputValue) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 3 5 (BitcoinFull.Base Bitcoin.InputValue) input_values_of
    f_simplicity_bitcoin_input_values_hash _inputValuesHash 144 input_values_sem words_bound_8).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** ** inputScriptsHash = hashWord256s32 (drop (primitive InputScriptHash)) *)
Definition input_scripts_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun x => from_hash256 x) (extInScriptHash e).

Lemma input_scripts_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 5)) (BitcoinFull.Ext BitcoinExt.InputScriptHash) i e =
    Some (match nth_error (input_scripts_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold input_scripts_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (extInScriptHash e) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_input_scripts_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_scripts_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (input_scripts_of e)) 0 176 432)
    (fun a environment =>
      @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptHash) input_scripts_of
    f_simplicity_bitcoin_input_scripts_hash _inputScriptsHash 176 input_scripts_sem words_bound_32).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** ** inputSequencesHash = hashWord32s (drop (primitive InputSequence)) *)
Definition input_sequences_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 2)) :=
  map (fun x => @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence x))) (sigTxIn (Bitcoin.envTx (extBase e))).

Lemma input_sequences_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 2)) (BitcoinFull.Base Bitcoin.InputSequence) i e =
    Some (match nth_error (input_sequences_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold input_sequences_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (sigTxIn (Bitcoin.envTx (extBase e))) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_input_sequences_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequences_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 2 5 (input_sequences_of e)) 0 240 432)
    (fun a environment =>
      @prim_words_hash_spec 2 5 (BitcoinFull.Base Bitcoin.InputSequence) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 2 5 (BitcoinFull.Base Bitcoin.InputSequence) input_sequences_of
    f_simplicity_bitcoin_input_sequences_hash _inputSequencesHash 240 input_sequences_sem words_bound_4).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** ** inputScriptSigsHash = hashWord256s32 (drop (primitive InputScriptSigHash)) *)
Definition input_script_sigs_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun x => from_hash256 x) (extInScriptSigHash e).

Lemma input_script_sigs_sem i e :
  @BitcoinFull.sem (Word 5) (Ty.Sum Ty.Unit (Vector (Word 3) 5)) (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) i e =
    Some (match nth_error (input_script_sigs_of e) (Z.to_nat (wz 5 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold input_script_sigs_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (extInScriptSigHash e) (Z.to_nat (@toZ (WordToZ 5) i))); reflexivity.
Qed.

Theorem bitcoin_input_script_sigs_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sigs_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 5 (input_script_sigs_of e)) 0 304 432)
    (fun a environment =>
      @prim_words_hash_spec 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) fullalg a environment).
Proof.
  apply (tx_words_hash_jet 5 5 (BitcoinFull.Ext BitcoinExt.InputScriptSigHash) input_script_sigs_of
    f_simplicity_bitcoin_input_script_sigs_hash _inputScriptSigsHash 304 input_script_sigs_sem words_bound_32).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.

(** The getters of a hash cached in the taproot environment. *)
Theorem tap_words_hash_jet k w p xs_of (f : function) (field : ident) (hdelta : Z) :
  (forall i e, @BitcoinFull.sem (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)) p i e =
    Some (match nth_error (xs_of e) (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_hash_mid_writeHash _taproot _bitcoinTapEnv field)) ->
  bitcoin_field_at _bitcoinTapEnv field hdelta ->
  0 <= hdelta /\ hdelta + 32 <= 176 ->
  application_jet_local_spec_sep f bitcoin_ge ext_environment Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of k w (xs_of e)) 8 hdelta 176)
    (fun a environment => @prim_words_hash_spec k w p fullalg a environment).
Proof.
  intros Hsem HB Hshape Hfield Hh.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _bitcoinTapEnv)
    (hashfield := field).
  - intros e. apply (prim_words_hash_spec_sem k w p xs_of Hsem HB).
  - exact Hshape.
  - exact bitcoin_txEnv_taproot.
  - exact Hfield.
  - lia.
  - exact Hh.
Qed.

Lemma words_bound_path : Z.of_nat (Nat.pow 2 5) * wsize 3 / 64 < ctx8_limit.
Proof. vm_compute. reflexivity. Qed.

(** ** tappathHash = hashWord256s8 (drop (primitive Tappath)) *)
Definition tappath_of (e : ext_environment) : list (Ty.tySem (Vector (Word 3) 5)) :=
  map (fun x => from_hash256 x) (extTappath e).

Lemma tappath_sem i e :
  @BitcoinFull.sem (Word 3) (Ty.Sum Ty.Unit (Vector (Word 3) 5)) (BitcoinFull.Ext BitcoinExt.Tappath) i e =
    Some (match nth_error (tappath_of e) (Z.to_nat (wz 3 i)) with
          | Some x => inr x | None => inl tt end).
Proof.
  unfold tappath_of. rewrite nth_error_map. unfold wz.
  cbn [BitcoinFull.sem]. unfold Bitcoin.sem, BitcoinExt.sem.
  destruct (nth_error (extTappath e) (Z.to_nat (@toZ (WordToZ 3) i))); reflexivity.
Qed.

Theorem bitcoin_tappath_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath_hash bitcoin_ge ext_environment
    Ty.Unit Word256
    (hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176)
    (fun a environment =>
      @prim_words_hash_spec 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) fullalg a environment).
Proof.
  apply (tap_words_hash_jet 5 3 (BitcoinFull.Ext BitcoinExt.Tappath) tappath_of
    f_simplicity_bitcoin_tappath_hash _tappathHash 40 tappath_sem words_bound_path).
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.
