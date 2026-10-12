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

Lemma ci_sizeof_SIN : sizeof sha_ge SIN = 160.
Proof. vm_compute; reflexivity. Qed.
Lemma ci_blockcopy_SIN : alignof_blockcopy sha_ge SIN = 8.
Proof. vm_compute; reflexivity. Qed.

Lemma envu_sigInput_annexHash : envu_field_at _sigInput _annexHash 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigInput_scriptSigHash : envu_field_at _sigInput _scriptSigHash 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigInput_prevOutpoint : envu_field_at _sigInput _prevOutpoint 64.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigInput_txo : envu_field_at _sigInput _txo 104.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigInput_sequence : envu_field_at _sigInput _sequence 144.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigInput_hasAnnex : envu_field_at _sigInput _hasAnnex 152.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_outpoint_txid : envu_field_at _outpoint _txid 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_outpoint_ix : envu_field_at _outpoint _ix 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_annex : envu_field_at _rawInput _annex 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_prevTxid : envu_field_at _rawInput _prevTxid 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_txo : envu_field_at _rawInput _txo 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_scriptSig : envu_field_at _rawInput _scriptSig 40.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_prevIx : envu_field_at _rawInput _prevIx 56.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawInput_sequence : envu_field_at _rawInput _sequence 60.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

(** Zero runs through an arbitrary midstate-typed expression. *)
Section ZeroRun.
Variables (e : env) (b : block) (a : expr) (delta : Z).
Hypothesis Ha : forall le m, eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr delta)).
Hypothesis Hty : typeof a = MID.
Hypothesis Hd : 0 <= delta <= 4000.

Lemma exec_zero_g le m m' k :
  (k < 8)%nat ->
  Mem.store Mint32 m b (delta + 4 * Z.of_nat k) (Vint Int.zero) = Some m' ->
  Clight2.exec_stmt sha_ge e le m (zero_g a k) E0 le m' Out_normal.
Proof.
  intros Hk HS.
  eapply exec_Sassign with (v2 := Vint Int.zero) (v := Vint Int.zero).
  - pose proof (eval_envu_field_array e le m a _sha256_midstate _s 0 A8 b (Ptrofs.repr delta)
      Hty envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl (Ha le m)) as HE.
    rewrite Ptrofs.add_zero in HE.
    eapply eval_Ederef. eapply eval_Ebinop; [exact HE|apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    assert (HU : Ptrofs.unsigned (Ptrofs.repr delta) = delta)
      by (apply Ptrofs.unsigned_repr; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite ptr_word_offset_from by (rewrite ?HU; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite HU. exact HS.
Qed.

Lemma zsr_exec n : forall lo, (lo + n <= 8)%nat ->
  forall acc le0 le m0 m1 m2,
  Clight2.exec_stmt sha_ge e le0 m0 acc E0 le m1 Out_normal ->
  store_words m1 b (delta + 4 * Z.of_nat lo) (repeat Int.zero n) = Some m2 ->
  Clight2.exec_stmt sha_ge e le0 m0 (zsr acc a lo n) E0 le m2 Out_normal.
Proof.
  induction n as [|n IH]; intros lo Hn acc le0 le m0 m1 m2 HA HS.
  - cbn in HS. injection HS as <-. exact HA.
  - rewrite repeat_snoc in HS. destruct (store_words_app_inv _ _ _ _ _ _ HS) as (mm & H1 & H2).
    rewrite repeat_length in H2. cbn [store_words] in H2.
    destruct (Mem.store Mint32 mm b (delta + 4 * Z.of_nat lo + 4 * Z.of_nat n) (Vint Int.zero)) as [mx|] eqn:HSt;
      [|discriminate].
    injection H2 as <-.
    cbn [zsr]. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply IH; [lia|exact HA|exact H1].
    + eapply exec_zero_g; [lia|].
      replace (delta + 4 * Z.of_nat (lo + n)) with (delta + 4 * Z.of_nat lo + 4 * Z.of_nat n) by lia. exact HSt.
Qed.
End ZeroRun.
