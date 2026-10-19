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

Ltac sepw := first [left; assumption
                   | right; left; try change (size_chunk Mptr) with 8; cbn [size_chunk]; rewrite ?repeat_length; lia
                   | right; right; try change (size_chunk Mptr) with 8; cbn [size_chunk]; rewrite ?repeat_length; lia].

Section TxFill.
Variables (e : env) (bCmp bA braw : block) (oraw : Z) (niv nov ver lt : int).
Hypothesis HeC : e!___compound = Some (bCmp, TX).
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis NCA : bCmp <> bA.
Hypothesis NrC : braw <> bCmp.

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let ni := Int.unsigned niv.
Let no := Int.unsigned nov.

Lemma ev_ctxn le m : eval_expr sha_ge e le m CTXN (Vptr bCmp Ptrofs.zero).
Proof. eapply eval_Elvalue; [apply eval_Evar_local; exact HeC|apply deref_loc_copy; reflexivity]. Qed.

Lemma ev_ctxn_mid le m f delta :
  envu_field_at _bitcoinTransaction f delta ->
  eval_expr sha_ge e le m (Efield CTXN f MID) (Vptr bCmp (Ptrofs.repr delta)).
Proof.
  intros Hf. pose proof (eval_envu_field_struct e le m CTXN _bitcoinTransaction f delta _sha256_midstate
    bCmp Ptrofs.zero eq_refl Hf (ev_ctxn le m)) as HE.
  rewrite Ptrofs.add_zero_l in HE. exact HE.
Qed.

Lemma exec_ctxn_store le m m' f delta ty chunk (a : expr) v2 v :
  envu_field_at _bitcoinTransaction f delta -> 0 <= delta <= 4000 ->
  access_mode ty = By_value chunk ->
  eval_expr sha_ge e le m a v2 -> sem_cast v2 (typeof a) ty m = Some v ->
  Mem.store chunk m bCmp delta v = Some m' ->
  Clight2.exec_stmt sha_ge e le m (Sassign (Efield CTXN f ty) a) E0 le m' Out_normal.
Proof.
  intros Hf Hd Hacc Hev Hcast HS.
  eapply exec_Sassign with (v2 := v2) (v := v).
  - eapply eval_envu_field_lvalue; [reflexivity|exact Hf|apply ev_ctxn].
  - exact Hev.
  - exact Hcast.
  - eapply assign_loc_value; [exact Hacc|]. unfold Mem.storev. rewrite mt_off by exact Hd. exact HS.
Qed.

(** What the allocated transaction holds after the copy (the members the
    rest of the function reads or keeps). *)
Definition mt_filled (m : mem) : Prop :=
  Mem.load Mptr m bA 0 = Some (Vptr bA (Ptrofs.repr 488)) /\
  Mem.load Mptr m bA 8 = Some (Vptr bA (Ptrofs.repr (488 + 160 * ni))) /\
  Mem.load Mint64 m bA 432 = Some (Vlong Int64.zero) /\
  Mem.load Mint64 m bA 440 = Some (Vlong Int64.zero) /\
  Mem.load Mint64 m bA 448 = Some (Vlong (Int64.repr ni)) /\
  Mem.load Mint64 m bA 456 = Some (Vlong (Int64.repr no)) /\
  Mem.load Mint64 m bA 464 = Some (Vlong (Int64.repr (Int.unsigned ver))) /\
  Mem.load Mint64 m bA 472 = Some (Vlong (Int64.repr (Int.unsigned lt))) /\
  Mem.load Mint8unsigned m bA 480 = Some (Vint Int.one).

Lemma mt_raw_field le m f delta v :
  le!_rawTx = Some rawv -> envu_field_at _rawBitcoinTransaction f delta -> 0 <= delta <= 36 ->
  Mem.load Mint32 m braw (oraw + delta) = Some (Vint v) ->
  eval_expr sha_ge e le m (Efield RAWTX f tuint) (Vint v).
Proof.
  intros Hle Hf Hd HL. eapply eval_envu_field_value;
    [reflexivity|exact Hf|reflexivity|apply eval_envu_deref_struct; exact Hle|].
  unfold rawv. rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

Theorem mt_fill_exec le1 m :
  mt_le1 le1 rawv bA ni ->
  Mem.load Mint32 m braw (oraw + 24) = Some (Vint niv) ->
  Mem.load Mint32 m braw (oraw + 28) = Some (Vint nov) ->
  Mem.load Mint32 m braw (oraw + 32) = Some (Vint ver) ->
  Mem.load Mint32 m braw (oraw + 36) = Some (Vint lt) ->
  Mem.range_perm m bCmp 0 488 Cur Writable ->
  Mem.range_perm m bA 0 488 Cur Writable ->
  exists m' le2,
    mt_filled m' /\ mt_le1 le2 rawv bA ni /\
    (forall ch b ofs, b <> bCmp -> (b <> bA \/ ofs + size_chunk ch <= 0 \/ 488 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    (forall t le' mf out,
       Clight2.exec_stmt sha_ge e le2 m' mt_rest2 t le' mf out ->
       Clight2.exec_stmt sha_ge e le1 m mt_rest1 t le' mf out).
Proof.
  intros (HlRaw & HlTx & HlIn & HlOut) HNi HNo HVer HLt PC PA.
  set (vin := Vptr bA (Ptrofs.repr 488)) in *.
  set (vout := Vptr bA (Ptrofs.repr (488 + 160 * ni))) in *.
  destruct (Mem.valid_access_store m Mptr bCmp 0 vin) as [mI SI].
  { split; [intros o Ho; change (size_chunk Mptr) with 8 in Ho; apply PC; lia|exists 0; reflexivity]. }
  destruct (Mem.valid_access_store mI Mptr bCmp 8 vout) as [mO SO].
  { split; [|exists 1; reflexivity]. intros o Ho. change (size_chunk Mptr) with 8 in Ho.
    eapply Mem.perm_store_1; [exact SI|]. apply PC. lia. }
  assert (PO : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mO b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact SO|]. eapply Mem.perm_store_1; [exact SI|exact Hp]. }
  destruct (store_words_exists (repeat Int.zero (8 * length mt_hash_fields)) mO bCmp 16) as [mW SW].
  { intros o Ho. rewrite repeat_length in Ho. apply PO, PC. cbn in Ho. lia. } { exists 4. reflexivity. }
  assert (PW : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mW b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW), PO, Hp. }
  assert (LW : forall ch b ofs, b <> bCmp -> Mem.load ch mW b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (store_words_load_other _ _ _ _ _ SW) by (left; exact Hb).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SO) by (left; exact Hb).
    apply (Mem.load_store_other _ _ _ _ _ _ SI). left. exact Hb. }
  destruct (Mem.valid_access_store mW Mint64 bCmp 432 (Vlong Int64.zero)) as [m1 S1].
  { split; [intros o Ho; change (size_chunk Mint64) with 8 in Ho; apply PW, PC; lia|exists 54; reflexivity]. }
  destruct (Mem.valid_access_store m1 Mint64 bCmp 440 (Vlong Int64.zero)) as [m2 S2].
  { split; [|exists 55; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S1|]. apply PW, PC. lia. }
  destruct (Mem.valid_access_store m2 Mint64 bCmp 448 (Vlong (Int64.repr ni))) as [m3 S3].
  { split; [|exists 56; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|]. apply PW, PC. lia. }
  destruct (Mem.valid_access_store m3 Mint64 bCmp 456 (Vlong (Int64.repr no))) as [m4 S4].
  { split; [|exists 57; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S3|]. eapply Mem.perm_store_1; [exact S2|].
    eapply Mem.perm_store_1; [exact S1|]. apply PW, PC. lia. }
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. eapply Mem.perm_store_1; [exact S3|].
    eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|]. apply PW, Hp. }
  destruct (Mem.valid_access_store m4 Mint64 bCmp 464 (Vlong (Int64.repr (Int.unsigned ver)))) as [m5 S5].
  { split; [intros o Ho; change (size_chunk Mint64) with 8 in Ho; apply P4, PC; lia|exists 58; reflexivity]. }
  destruct (Mem.valid_access_store m5 Mint64 bCmp 472 (Vlong (Int64.repr (Int.unsigned lt)))) as [m6 S6].
  { split; [|exists 59; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S5|]. apply P4, PC. lia. }
  destruct (Mem.valid_access_store m6 Mint8unsigned bCmp 480 (Vint Int.one)) as [mF S7].
  { split; [|exists 480; reflexivity]. intros o Ho. change (size_chunk Mint8unsigned) with 1 in Ho.
    eapply Mem.perm_store_1; [exact S6|]. eapply Mem.perm_store_1; [exact S5|]. apply P4, PC. lia. }
  assert (PF : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mF b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S7|]. eapply Mem.perm_store_1; [exact S6|].
    eapply Mem.perm_store_1; [exact S5|]. apply P4, Hp. }
  assert (L1 : forall ch b ofs, b <> bCmp -> Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S1) by (left; exact Hb). apply LW, Hb. }
  assert (L2 : forall ch b ofs, b <> bCmp -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (left; exact Hb). apply L1, Hb. }
  assert (L3 : forall ch b ofs, b <> bCmp -> Mem.load ch m3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S3) by (left; exact Hb). apply L2, Hb. }
  assert (L4 : forall ch b ofs, b <> bCmp -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (left; exact Hb). apply L3, Hb. }
  assert (L5 : forall ch b ofs, b <> bCmp -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by (left; exact Hb). apply L4, Hb. }
  assert (LF : forall ch b ofs, b <> bCmp -> Mem.load ch mF b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by (left; exact Hb).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by (left; exact Hb). apply L5, Hb. }
  (* the copy *)
  destruct (Mem.range_perm_loadbytes mF bCmp 0 488) as (bytes & HCB).
  { intros o Ho. eapply Mem.perm_implies; [apply PF, PC, Ho|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCB) as HCBL.
  destruct (Mem.range_perm_storebytes mF bA 0 bytes) as (mG & SG).
  { rewrite HCBL. intros o Ho. change (Z.of_nat (Z.to_nat 488)) with 488 in Ho. apply PF, PA. lia. }
  assert (HGB : Mem.loadbytes mG bA 0 488 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SG) as H. rewrite HCBL in H. exact H. }
  (* contents of the compound *)
  assert (C0 : Mem.load Mptr mF bCmp 0 = Some vin).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S3) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S1) by sepw. rewrite (store_words_load_other _ _ _ _ _ SW) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ SO) by sepw. rewrite (Mem.load_store_same _ _ _ _ _ _ SI). reflexivity. }
  assert (C8 : Mem.load Mptr mF bCmp 8 = Some vout).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S3) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S1) by sepw. rewrite (store_words_load_other _ _ _ _ _ SW) by sepw.
    rewrite (Mem.load_store_same _ _ _ _ _ _ SO). reflexivity. }
  assert (C432 : Mem.load Mint64 mF bCmp 432 = Some (Vlong Int64.zero)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S3) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by sepw.
    rewrite (Mem.load_store_same _ _ _ _ _ _ S1). reflexivity. }
  assert (C440 : Mem.load Mint64 mF bCmp 440 = Some (Vlong Int64.zero)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S3) by sepw. rewrite (Mem.load_store_same _ _ _ _ _ _ S2). reflexivity. }
  assert (C448 : Mem.load Mint64 mF bCmp 448 = Some (Vlong (Int64.repr ni))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by sepw.
    rewrite (Mem.load_store_same _ _ _ _ _ _ S3). reflexivity. }
  assert (C456 : Mem.load Mint64 mF bCmp 456 = Some (Vlong (Int64.repr no))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by sepw. rewrite (Mem.load_store_same _ _ _ _ _ _ S4). reflexivity. }
  assert (C464 : Mem.load Mint64 mF bCmp 464 = Some (Vlong (Int64.repr (Int.unsigned ver)))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by sepw.
    rewrite (Mem.load_store_same _ _ _ _ _ _ S5). reflexivity. }
  assert (C472 : Mem.load Mint64 mF bCmp 472 = Some (Vlong (Int64.repr (Int.unsigned lt)))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S7) by sepw. rewrite (Mem.load_store_same _ _ _ _ _ _ S6). reflexivity. }
  assert (C480 : Mem.load Mint8unsigned mF bCmp 480 = Some (Vint Int.one)).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ S7). reflexivity. }
  set (la := PTree.set _t'22 (Vint niv) le1).
  set (lb := PTree.set _t'21 (Vint nov) la).
  set (lc := PTree.set _t'20 (Vint ver) lb).
  set (ld := PTree.set _t'19 (Vint lt) lc).
  assert (Hla : la!_rawTx = Some rawv) by (unfold la; rewrite PTree.gso by discriminate; exact HlRaw).
  assert (Hlb : lb!_rawTx = Some rawv) by (unfold lb; rewrite PTree.gso by discriminate; exact Hla).
  assert (Hlc : lc!_rawTx = Some rawv) by (unfold lc; rewrite PTree.gso by discriminate; exact Hlb).
  exists mG, ld.
  split.
  { unfold mt_filled.
    split; [apply (equal_loadbytes_field Mptr mF mG bCmp bA 0 0 488 0 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 0; reflexivity|exact C0]|].
    split; [apply (equal_loadbytes_field Mptr mF mG bCmp bA 0 0 488 8 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 1; reflexivity|exact C8]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 432 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 54; reflexivity|exact C432]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 440 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 55; reflexivity|exact C440]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 448 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 56; reflexivity|exact C448]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 456 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 57; reflexivity|exact C456]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 464 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 58; reflexivity|exact C464]|].
    split; [apply (equal_loadbytes_field Mint64 mF mG bCmp bA 0 0 488 472 bytes);
            [lia|cbn; lia|exact HCB|exact HGB|exists 59; reflexivity|exact C472]|].
    apply (equal_loadbytes_field Mint8unsigned mF mG bCmp bA 0 0 488 480 bytes);
      [lia|cbn; lia|exact HCB|exact HGB|apply Z.divide_1_l|exact C480]. }
  split.
  { unfold mt_le1, ld, lc, lb, la. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  split.
  { intros ch b ofs Hb Hr. rewrite (Mem.load_storebytes_other _ _ _ _ _ SG).
    - apply LF, Hb.
    - rewrite HCBL. change (Z.of_nat (Z.to_nat 488)) with 488.
      destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]. }
  split; [intros b ofs k p Hp; eapply Mem.perm_storebytes_1; [exact SG|apply PF, Hp]|].
  split.
  { intros b Hb. eapply Mem.storebytes_valid_block_1; [exact SG|].
    eapply Mem.store_valid_block_1; [exact S7|]. eapply Mem.store_valid_block_1; [exact S6|].
    eapply Mem.store_valid_block_1; [exact S5|]. eapply Mem.store_valid_block_1; [exact S4|].
    eapply Mem.store_valid_block_1; [exact S3|]. eapply Mem.store_valid_block_1; [exact S2|].
    eapply Mem.store_valid_block_1; [exact S1|].
    unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ SW).
    eapply Mem.store_valid_block_1; [exact SO|]. eapply Mem.store_valid_block_1; [exact SI|exact Hb]. }
  intros t le' mf out HRest. rewrite mt_rest1_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := ld) (m1 := mG); [|exact HRest].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := ld) (m1 := mF).
  - rewrite mt_fill_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := ld) (m1 := m6).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lc) (m1 := m5).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lb) (m1 := m4).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := la) (m1 := m3).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m2).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mW).
                     +++ eapply (zsl_exec e bCmp _ 16) with (m1 := mO); [| | | |rewrite map_length; exact SW].
                         *** intros i a Hn. rewrite nth_error_map in Hn.
                             destruct (nth_error mt_hash_fields i) as [f|] eqn:Ef; [|discriminate].
                             injection Hn as <-. split; [reflexivity|].
                             intros leq mq. apply ev_ctxn_mid. apply mt_hash_offsets. exact Ef.
                         *** lia.
                         *** rewrite map_length. cbn. lia.
                         *** unfold mt_fill_ptrs.
                             eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mI).
                             ---- eapply exec_ctxn_store with (delta := 0) (chunk := Mptr);
                                    [exact envu_tx_input|lia|reflexivity|apply eval_Etempvar; exact HlIn|reflexivity|exact SI].
                             ---- eapply exec_ctxn_store with (delta := 8) (chunk := Mptr);
                                    [exact envu_tx_output|lia|reflexivity|apply eval_Etempvar; exact HlOut|reflexivity|exact SO].
                     +++ eapply exec_ctxn_store with (delta := 432) (chunk := Mint64);
                           [exact envu_tx_totalInputValue|lia|reflexivity|apply eval_Econst_int|reflexivity|exact S1].
                 --- eapply exec_ctxn_store with (delta := 440) (chunk := Mint64);
                       [exact envu_tx_totalOutputValue|lia|reflexivity|apply eval_Econst_int|reflexivity|exact S2].
              ** unfold mt_scalar.
                 eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := la) (m1 := m2).
                 --- apply exec_Sset. eapply mt_raw_field with (delta := 24); [exact HlRaw|exact envu_rawTx_numInputs|lia|].
                     rewrite L2 by exact NrC. exact HNi.
                 --- eapply exec_ctxn_store with (delta := 448) (chunk := Mint64);
                       [exact envu_tx_numInputs|lia|reflexivity|apply eval_Etempvar; apply PTree.gss|reflexivity|exact S3].
           ++ unfold mt_scalar.
              eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lb) (m1 := m3).
              ** apply exec_Sset. eapply mt_raw_field with (delta := 28); [exact Hla|exact envu_rawTx_numOutputs|lia|].
                 rewrite L3 by exact NrC. exact HNo.
              ** eapply exec_ctxn_store with (delta := 456) (chunk := Mint64);
                   [exact envu_tx_numOutputs|lia|reflexivity|apply eval_Etempvar; apply PTree.gss|reflexivity|exact S4].
        -- unfold mt_scalar.
           eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lc) (m1 := m4).
           ++ apply exec_Sset. eapply mt_raw_field with (delta := 32); [exact Hlb|exact envu_rawTx_version|lia|].
              rewrite L4 by exact NrC. exact HVer.
           ++ eapply exec_ctxn_store with (delta := 464) (chunk := Mint64);
                [exact envu_tx_version|lia|reflexivity|apply eval_Etempvar; apply PTree.gss|reflexivity|exact S5].
      * unfold mt_scalar.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := ld) (m1 := m5).
        -- apply exec_Sset. eapply mt_raw_field with (delta := 36); [exact Hlc|exact envu_rawTx_lockTime|lia|].
           rewrite L5 by exact NrC. exact HLt.
        -- eapply exec_ctxn_store with (delta := 472) (chunk := Mint64);
             [exact envu_tx_lockTime|lia|reflexivity|apply eval_Etempvar; apply PTree.gss|reflexivity|exact S6].
    + eapply exec_ctxn_store with (delta := 480) (chunk := Mint8unsigned);
        [exact envu_tx_isFinal|lia|reflexivity|apply eval_Econst_int|reflexivity|exact S7].
  - unfold mt_copy.
    eapply exec_Sassign with (v2 := Vptr bCmp Ptrofs.zero) (v := Vptr bCmp Ptrofs.zero).
    + eapply eval_Ederef. apply eval_Etempvar. unfold ld, lc, lb, la. rewrite !PTree.gso by discriminate. exact HlTx.
    + apply ev_ctxn.
    + reflexivity.
    + eapply assign_loc_copy with (bytes := bytes); cbn [typeof].
      * reflexivity.
      * intros _. rewrite mt_blockcopy_TX. exists 0. reflexivity.
      * intros _. rewrite mt_blockcopy_TX. exists 0. reflexivity.
      * left. exact NCA.
      * rewrite mt_sizeof_TX_Z. exact HCB.
      * exact SG.
Qed.
End TxFill.
