(** [copyInput(result, input)] (bitcoin/env.c), first part: the compound
    literal
      *result = (sigInput){ .prevOutpoint = { .ix = input->prevIx },
                            .sequence = input->sequence, .hasAnnex = !!input->annex };
    built in the local [__compound] and copied to [*result]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_struct_copy_loads.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_be32_exec.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_fill C.jet_bitcoin_env_copyoutput.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation SIN := (Tstruct _sigInput noattr).
Notation RIN := (Tstruct _rawInput noattr).
Notation OP := (Tstruct _outpoint noattr).
Notation CIN := (Evar ___compound SIN).

Definition ci_body : statement := fn_body f_copyInput.
(** [ci_body = Ssequence (Ssequence ci_fill ci_copy) ci_rest]. *)
Definition ci_fill : statement :=
  ltac:(let b := eval cbv delta [ci_body f_copyInput fn_body] beta iota in ci_body in
        lazymatch b with Ssequence (Ssequence ?f _) _ => exact f end).
Definition ci_rest : statement :=
  ltac:(let b := eval cbv delta [ci_body f_copyInput fn_body] beta iota in ci_body in
        lazymatch b with Ssequence _ ?r => exact r end).
Definition ci_copy : statement :=
  Sassign (Ederef (Etempvar _result (tptr SIN)) SIN) CIN.

Lemma ci_body_shape : ci_body = Ssequence (Ssequence ci_fill ci_copy) ci_rest.
Proof. reflexivity. Qed.

(** Zeroing the eight words of a midstate designated by an expression. *)
Definition zero_g (a : expr) (k : nat) : statement :=
  Sassign (Ederef (Ebinop Oadd (Efield a _s A8)
    (Econst_int (Int.repr (Z.of_nat k)) tint) (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint).

Fixpoint zsr (acc : statement) (a : expr) (lo n : nat) : statement :=
  match n with
  | O => acc
  | S k => Ssequence (zsr acc a lo k) (zero_g a (lo + k))
  end.

Definition ci_ix : statement :=
  Ssequence (Sset _t'6 (Efield (Ederef (Etempvar _input (tptr RIN)) RIN) _prevIx tuint))
    (Sassign (Efield (Efield CIN _prevOutpoint OP) _ix tulong) (Etempvar _t'6 tuint)).
Definition ci_value : statement :=
  Sassign (Efield (Efield CIN _txo SOUT) _value tulong) (Econst_int (Int.repr 0) tint).
Definition ci_sequence : statement :=
  Ssequence (Sset _t'5 (Efield (Ederef (Etempvar _input (tptr RIN)) RIN) _sequence tuint))
    (Sassign (Efield CIN _sequence tulong) (Etempvar _t'5 tuint)).
Definition ci_hasAnnex : statement :=
  Ssequence (Sset _t'4 (Efield (Ederef (Etempvar _input (tptr RIN)) RIN) _annex (tptr RBUF)))
    (Sassign (Efield CIN _hasAnnex tbool)
      (Eunop Onotbool (Eunop Onotbool (Etempvar _t'4 (tptr RBUF)) tint) tint)).

Lemma ci_fill_shape : ci_fill =
  Ssequence
    (Ssequence
      (zsr (Ssequence
             (Ssequence
               (zsr (zsr (zsr (zero_g (Efield CIN _annexHash MID) 0) (Efield CIN _annexHash MID) 1 7)
                         (Efield CIN _scriptSigHash MID) 0 8)
                    (Efield (Efield CIN _prevOutpoint OP) _txid MID) 0 8)
               ci_ix)
             ci_value)
           (Efield (Efield CIN _txo SOUT) _scriptPubKey MID) 0 8)
      ci_sequence)
    ci_hasAnnex.
Proof. reflexivity. Qed.
