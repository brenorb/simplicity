(** [simplicity_bitcoin_mallocTransaction], second part: the compound
    literal
      *tx = (bitcoinTransaction){ .input = input, .output = output,
              .numInputs = rawTx->numInputs, .numOutputs = rawTx->numOutputs,
              .version = rawTx->version, .lockTime = rawTx->lockTime, .isFinal = true };
    built in the local [__compound] (thirteen zeroed midstates, zero totals)
    and copied to the allocated block. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_struct_copy_loads.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_be32_exec.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_fill.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_tx_prelude.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation CTXN := (Evar ___compound TX).
Notation RAWTX := (Ederef (Etempvar _rawTx (tptr RTX)) RTX).

(** [mt_rest1 = Ssequence (Ssequence mt_fill mt_copy) mt_rest2]. *)
Definition mt_fill : statement :=
  ltac:(let b := eval cbv delta [mt_rest1] in mt_rest1 in
        lazymatch b with Ssequence (Ssequence ?f _) _ => exact f end).
Definition mt_rest2 : statement :=
  ltac:(let b := eval cbv delta [mt_rest1] in mt_rest1 in
        lazymatch b with Ssequence _ ?r => exact r end).
Definition mt_copy : statement := Sassign (Ederef (Etempvar _tx (tptr TX)) TX) CTXN.

Lemma mt_rest1_shape : mt_rest1 = Ssequence (Ssequence mt_fill mt_copy) mt_rest2.
Proof. reflexivity. Qed.

(** Zero runs over a list of midstate expressions. *)
Definition zsl (acc : statement) (l : list expr) : statement :=
  fold_left (fun acc a => zsr acc a 0 8) l acc.

Definition mt_hash_fields : list ident :=
  [_outputValuesHash; _outputScriptsHash; _outputsHash; _inputOutpointsHash; _inputValuesHash;
   _inputScriptsHash; _inputUTXOsHash; _inputSequencesHash; _inputAnnexesHash; _inputScriptSigsHash;
   _inputsHash; _txHash; _txid].

Definition mt_scalar (raw cmp : ident) (t : ident) : statement :=
  Ssequence (Sset t (Efield RAWTX raw tuint)) (Sassign (Efield CTXN cmp tulong) (Etempvar t tuint)).

Definition mt_fill_ptrs : statement :=
  Ssequence (Sassign (Efield CTXN _input (tptr SIN)) (Etempvar _input (tptr SIN)))
            (Sassign (Efield CTXN _output (tptr SOUT)) (Etempvar _output (tptr SOUT))).

Lemma mt_fill_shape : mt_fill =
  Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (zsl mt_fill_ptrs (map (fun f => Efield CTXN f MID) mt_hash_fields))
                (Sassign (Efield CTXN _totalInputValue tulong) (Econst_int (Int.repr 0) tint)))
              (Sassign (Efield CTXN _totalOutputValue tulong) (Econst_int (Int.repr 0) tint)))
            (mt_scalar _numInputs _numInputs _t'22))
          (mt_scalar _numOutputs _numOutputs _t'21))
        (mt_scalar _version _version _t'20))
      (mt_scalar _lockTime _lockTime _t'19))
    (Sassign (Efield CTXN _isFinal tbool) (Econst_int (Int.repr 1) tint)).
Proof. reflexivity. Qed.

Lemma mt_sizeof_TX_Z : sizeof sha_ge TX = 488.
Proof. vm_compute; reflexivity. Qed.
Lemma mt_blockcopy_TX : alignof_blockcopy sha_ge TX = 8.
Proof. vm_compute; reflexivity. Qed.

Lemma mt_hash_offsets i f : nth_error mt_hash_fields i = Some f ->
  envu_field_at _bitcoinTransaction f (16 + 32 * Z.of_nat i).
Proof.
  intros H. unfold mt_hash_fields in H.
  do 13 (destruct i as [|i]; cbn [nth_error] in H;
    [injection H as <-; apply envu_field_offset_at; vm_compute; reflexivity|]).
  destruct i; cbn [nth_error] in H; discriminate H.
Qed.

Lemma envu_tx_input : envu_field_at _bitcoinTransaction _input 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_output : envu_field_at _bitcoinTransaction _output 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_totalInputValue : envu_field_at _bitcoinTransaction _totalInputValue 432.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_totalOutputValue : envu_field_at _bitcoinTransaction _totalOutputValue 440.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_numInputs : envu_field_at _bitcoinTransaction _numInputs 448.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_numOutputs : envu_field_at _bitcoinTransaction _numOutputs 456.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_version : envu_field_at _bitcoinTransaction _version 464.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_lockTime : envu_field_at _bitcoinTransaction _lockTime 472.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_tx_isFinal : envu_field_at _bitcoinTransaction _isFinal 480.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawTx_version : envu_field_at _rawBitcoinTransaction _version 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawTx_lockTime : envu_field_at _rawBitcoinTransaction _lockTime 36.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma mt_off delta : 0 <= delta <= 4000 ->
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta)) = delta.
Proof.
  intros H. rewrite Ptrofs.add_zero_l. apply Ptrofs.unsigned_repr.
  change Ptrofs.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma store_words_repeat_split z n1 n2 m b base m2 :
  store_words m b base (repeat z (n1 + n2)) = Some m2 ->
  exists m1, store_words m b base (repeat z n1) = Some m1 /\
    store_words m1 b (base + 4 * Z.of_nat n1) (repeat z n2) = Some m2.
Proof.
  intros H. rewrite repeat_app in H. destruct (store_words_app_inv _ _ _ _ _ _ H) as (m1 & H1 & H2).
  rewrite repeat_length in H2. exists m1. split; assumption.
Qed.

Lemma zsl_exec e b : forall (l : list expr) base acc le0 le m0 m1 m2,
  (forall i a, nth_error l i = Some a ->
     typeof a = MID /\ forall le' m', eval_expr sha_ge e le' m' a (Vptr b (Ptrofs.repr (base + 32 * Z.of_nat i)))) ->
  0 <= base -> base + 32 * Z.of_nat (length l) <= 4000 ->
  Clight2.exec_stmt sha_ge e le0 m0 acc E0 le m1 Out_normal ->
  store_words m1 b base (repeat Int.zero (8 * length l)) = Some m2 ->
  Clight2.exec_stmt sha_ge e le0 m0 (zsl acc l) E0 le m2 Out_normal.
Proof.
  induction l as [|a l IH]; intros base acc le0 le m0 m1 m2 HE Hb HbM HA HS.
  - cbn in HS. injection HS as <-. exact HA.
  - cbn [length] in HbM, HS. replace (8 * S (length l))%nat with (8 + 8 * length l)%nat in HS by lia.
    destruct (store_words_repeat_split _ _ _ _ _ _ _ HS) as (mm & H1 & H2).
    destruct (HE 0%nat a eq_refl) as [Hty Hev]. rewrite Z.mul_0_r, Z.add_0_r in Hev.
    unfold zsl. cbn [fold_left]. fold (zsl (zsr acc a 0 8) l).
    eapply (IH (base + 32)); [| | | |replace (base + 32) with (base + 4 * Z.of_nat 8) by lia; exact H2].
    + intros i a' Hn. destruct (HE (S i) a' Hn) as [Hty' Hev']. split; [exact Hty'|].
      intros le' m'. replace (base + 32 + 32 * Z.of_nat i) with (base + 32 * Z.of_nat (S i)) by lia. apply Hev'.
    + lia.
    + lia.
    + eapply (zsr_exec e b a base Hev Hty ltac:(lia) 8 0%nat ltac:(lia)); [exact HA|].
      rewrite Z.mul_0_r, Z.add_0_r. exact H1.
Qed.
