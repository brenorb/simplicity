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
