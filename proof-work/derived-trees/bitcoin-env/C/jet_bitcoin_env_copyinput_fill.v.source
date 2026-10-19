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

Lemma ci_bool_cast (h : int) : h = Int.zero \/ h = Int.one ->
  (if Int.eq h Int.zero then Int.zero else Int.one) = h.
Proof. intros [-> | ->]; reflexivity. Qed.

Section CopyInputFill.
Variables (e : env) (bCmp bres bin : block) (ores oin : Z) (ix sq hasv : int) (vannex : val).
Hypothesis HeC : e!___compound = Some (bCmp, SIN).
Hypothesis Hores : 0 <= ores /\ ores + 160 <= Ptrofs.max_unsigned.
Hypothesis HoA : (8 | ores).
Hypothesis Hoin : 0 <= oin /\ oin + 64 <= Ptrofs.max_unsigned.
Hypothesis NCr : bCmp <> bres.
Hypothesis NiC : bin <> bCmp.

Lemma ev_cin le m : eval_expr sha_ge e le m CIN (Vptr bCmp Ptrofs.zero).
Proof. eapply eval_Elvalue; [apply eval_Evar_local; exact HeC|apply deref_loc_copy; reflexivity]. Qed.

Lemma ev_cin_field le m f delta sid :
  envu_field_at _sigInput f delta ->
  eval_expr sha_ge e le m (Efield CIN f (Tstruct sid noattr)) (Vptr bCmp (Ptrofs.repr delta)).
Proof.
  intros Hf. pose proof (eval_envu_field_struct e le m CIN _sigInput f delta sid bCmp Ptrofs.zero
    eq_refl Hf (ev_cin le m)) as HE.
  rewrite Ptrofs.add_zero_l in HE. exact HE.
Qed.

Lemma ev_cin_txid le m :
  eval_expr sha_ge e le m (Efield (Efield CIN _prevOutpoint OP) _txid MID) (Vptr bCmp (Ptrofs.repr 64)).
Proof.
  pose proof (eval_envu_field_struct e le m (Efield CIN _prevOutpoint OP) _outpoint _txid 0 _sha256_midstate
    bCmp (Ptrofs.repr 64) eq_refl envu_outpoint_txid (ev_cin_field le m _ 64 _ envu_sigInput_prevOutpoint)) as HE.
  rewrite Ptrofs.add_zero in HE. exact HE.
Qed.

Lemma ev_cin_spk le m :
  eval_expr sha_ge e le m (Efield (Efield CIN _txo SOUT) _scriptPubKey MID) (Vptr bCmp (Ptrofs.repr 112)).
Proof.
  pose proof (eval_envu_field_struct e le m (Efield CIN _txo SOUT) _sigOutput _scriptPubKey 8 _sha256_midstate
    bCmp (Ptrofs.repr 104) eq_refl envu_sigOutput_scriptPubKey (ev_cin_field le m _ 104 _ envu_sigInput_txo)) as HE.
  rewrite envu_ptr_add_repr in HE by (change Ptrofs.max_unsigned with 18446744073709551615; lia). exact HE.
Qed.

(** What [*result] holds after the copy (the fields the rest of the function
    does not overwrite). *)
Definition ci_filled (m : mem) : Prop :=
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bres (ores + 4 * Z.of_nat j) = Some (Vint Int.zero)) /\
  Mem.load Mint64 m bres (ores + 96) = Some (Vlong (Int64.repr (Int.unsigned ix))) /\
  Mem.load Mint64 m bres (ores + 144) = Some (Vlong (Int64.repr (Int.unsigned sq))) /\
  Mem.load Mint8unsigned m bres (ores + 152) = Some (Vint hasv).

Theorem ci_fill_exec le0 m :
  le0!_result = Some (Vptr bres (Ptrofs.repr ores)) ->
  le0!_input = Some (Vptr bin (Ptrofs.repr oin)) ->
  Mem.load Mptr m bin oin = Some vannex ->
  Mem.load Mint32 m bin (oin + 56) = Some (Vint ix) ->
  Mem.load Mint32 m bin (oin + 60) = Some (Vint sq) ->
  (vannex = Vlong Int64.zero /\ hasv = Int.zero) \/
  (exists ba oa, vannex = Vptr ba oa /\ Mem.perm m ba (Ptrofs.unsigned oa) Cur Nonempty /\ hasv = Int.one) ->
  Mem.range_perm m bCmp 0 160 Cur Writable ->
  Mem.range_perm m bres ores (ores + 160) Cur Writable ->
  exists m' le1,
    ci_filled m' /\
    le1!_result = Some (Vptr bres (Ptrofs.repr ores)) /\ le1!_input = Some (Vptr bin (Ptrofs.repr oin)) /\
    (forall ch b ofs, b <> bCmp -> (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 160 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    (forall t le' mf out,
       Clight2.exec_stmt sha_ge e le1 m' ci_rest t le' mf out ->
       Clight2.exec_stmt sha_ge e le0 m ci_body t le' mf out).
Proof.
  intros HlR HlI HAnx HIx HSq HAn PC PR.
  (* annexHash, scriptSigHash, txid: zero *)
  destruct (store_words_exists (repeat Int.zero 8) m bCmp 0) as [mW1 SW1].
  { intros o Ho. rewrite repeat_length in Ho. apply PC. lia. } { exists 0. reflexivity. }
  destruct (store_words_exists (repeat Int.zero 8) mW1 bCmp 32) as [mW2 SW2].
  { intros o Ho. rewrite repeat_length in Ho. apply (store_words_perm _ _ _ _ _ SW1), PC. lia. } { exists 8. reflexivity. }
  destruct (store_words_exists (repeat Int.zero 8) mW2 bCmp 64) as [mW3 SW3].
  { intros o Ho. rewrite repeat_length in Ho.
    apply (store_words_perm _ _ _ _ _ SW2), (store_words_perm _ _ _ _ _ SW1), PC. lia. } { exists 16. reflexivity. }
  assert (P3 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mW3 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW3), (store_words_perm _ _ _ _ _ SW2),
      (store_words_perm _ _ _ _ _ SW1), Hp. }
  assert (L3 : forall ch b ofs, b <> bCmp -> Mem.load ch mW3 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (store_words_load_other _ _ _ _ _ SW3) by (left; exact Hb).
    rewrite (store_words_load_other _ _ _ _ _ SW2) by (left; exact Hb).
    apply (store_words_load_other _ _ _ _ _ SW1). left. exact Hb. }
  (* ix, value *)
  destruct (Mem.valid_access_store mW3 Mint64 bCmp 96 (Vlong (Int64.repr (Int.unsigned ix)))) as [mI SI].
  { split; [intros o Ho; change (size_chunk Mint64) with 8 in Ho; apply P3, PC; lia|exists 12; reflexivity]. }
  destruct (Mem.valid_access_store mI Mint64 bCmp 104 (Vlong Int64.zero)) as [mV SV].
  { split; [|exists 13; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_store_1; [exact SI|]. apply P3, PC. lia. }
  assert (PV : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mV b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact SV|]. eapply Mem.perm_store_1; [exact SI|apply P3, Hp]. }
  (* scriptPubKey: zero *)
  destruct (store_words_exists (repeat Int.zero 8) mV bCmp 112) as [mW4 SW4].
  { intros o Ho. rewrite repeat_length in Ho. apply PV, PC. lia. } { exists 28. reflexivity. }
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mW4 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW4), PV, Hp. }
  assert (L4 : forall ch b ofs, b <> bCmp -> Mem.load ch mW4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (store_words_load_other _ _ _ _ _ SW4) by (left; exact Hb).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SV) by (left; exact Hb).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SI) by (left; exact Hb). apply L3, Hb. }
  (* sequence, hasAnnex *)
  destruct (Mem.valid_access_store mW4 Mint64 bCmp 144 (Vlong (Int64.repr (Int.unsigned sq)))) as [mS SS].
  { split; [intros o Ho; change (size_chunk Mint64) with 8 in Ho; apply P4, PC; lia|exists 18; reflexivity]. }
  destruct (Mem.valid_access_store mS Mint8unsigned bCmp 152 (Vint hasv)) as [mF SF].
  { split; [|exists 152; reflexivity]. intros o Ho. change (size_chunk Mint8unsigned) with 1 in Ho.
    eapply Mem.perm_store_1; [exact SS|]. apply P4, PC. lia. }
  assert (PF : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mF b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact SF|]. eapply Mem.perm_store_1; [exact SS|apply P4, Hp]. }
  assert (LS : forall ch b ofs, b <> bCmp -> Mem.load ch mS b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (left; exact Hb). apply L4, Hb. }
  assert (LF : forall ch b ofs, b <> bCmp -> Mem.load ch mF b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ SF) by (left; exact Hb). apply LS, Hb. }
  (* the copy *)
  destruct (Mem.range_perm_loadbytes mF bCmp 0 160) as (bytes & HCB).
  { intros o Ho. eapply Mem.perm_implies; [apply PF, PC, Ho|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCB) as HCBL.
  destruct (Mem.range_perm_storebytes mF bres ores bytes) as (mG & SG).
  { rewrite HCBL. intros o Ho. change (Z.of_nat (Z.to_nat 160)) with 160 in Ho. apply PF, PR. lia. }
  assert (HGB : Mem.loadbytes mG bres ores 160 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SG) as H. rewrite HCBL in H. exact H. }
  (* contents of the compound *)
  assert (C1 : forall j, (j < 8)%nat -> Mem.load Mint32 mF bCmp (0 + 4 * Z.of_nat j) = Some (Vint Int.zero)).
  { intros j Hj.
    rewrite (Mem.load_store_other _ _ _ _ _ _ SF) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW4) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SV) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SI) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW3) by (right; left; change (size_chunk Mint32) with 4; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW2) by (right; left; change (size_chunk Mint32) with 4; lia).
    pose proof (jet_sha_add_n_calls.u32_nth mW1 bCmp 0 (repeat Int.zero 8)
      (store_words_loads _ _ _ _ _ SW1) j ltac:(rewrite repeat_length; exact Hj)) as H.
    rewrite nth_repeat in H. exact H. }
  assert (C2 : Mem.load Mint64 mF bCmp 96 = Some (Vlong (Int64.repr (Int.unsigned ix)))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ SF) by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SS) by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW4) by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ SV) by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ SI). reflexivity. }
  assert (C3 : Mem.load Mint64 mF bCmp 144 = Some (Vlong (Int64.repr (Int.unsigned sq)))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ SF) by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ SS). reflexivity. }
  assert (Hh01 : hasv = Int.zero \/ hasv = Int.one).
  { destruct HAn as [[_ ->]|(ba & oa & _ & _ & ->)]; [left|right]; reflexivity. }
  assert (C4 : Mem.load Mint8unsigned mF bCmp 152 = Some (Vint hasv)).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ SF). cbn.
    destruct Hh01 as [-> | ->]; reflexivity. }
  set (le1 := PTree.set _t'6 (Vint ix) le0).
  set (le2 := PTree.set _t'5 (Vint sq) le1).
  set (le3 := PTree.set _t'4 vannex le2).
  assert (HlI1 : le1!_input = Some (Vptr bin (Ptrofs.repr oin))) by (unfold le1; rewrite PTree.gso by discriminate; exact HlI).
  assert (HlI2 : le2!_input = Some (Vptr bin (Ptrofs.repr oin))) by (unfold le2; rewrite PTree.gso by discriminate; exact HlI1).
  exists mG, le3.
  split.
  { split; [|split; [|split]].
    - intros j Hj. apply (equal_loadbytes_field Mint32 mF mG bCmp bres 0 ores 160 (4 * Z.of_nat j) bytes);
        [lia|change (size_chunk Mint32) with 4; lia|exact HCB|exact HGB| |apply C1; exact Hj].
      change (align_chunk Mint32) with 4. destruct HoA as [q ->]. exists (2 * q + Z.of_nat j). lia.
    - apply (equal_loadbytes_field Mint64 mF mG bCmp bres 0 ores 160 96 bytes);
        [lia|cbn; lia|exact HCB|exact HGB| |exact C2].
      change (align_chunk Mint64) with 8. destruct HoA as [q ->]. exists (q + 12). lia.
    - apply (equal_loadbytes_field Mint64 mF mG bCmp bres 0 ores 160 144 bytes);
        [lia|cbn; lia|exact HCB|exact HGB| |exact C3].
      change (align_chunk Mint64) with 8. destruct HoA as [q ->]. exists (q + 18). lia.
    - apply (equal_loadbytes_field Mint8unsigned mF mG bCmp bres 0 ores 160 152 bytes);
        [lia|cbn; lia|exact HCB|exact HGB|apply Z.divide_1_l|exact C4]. }
  split; [unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact HlR|].
  split; [unfold le3; rewrite PTree.gso by discriminate; exact HlI2|].
  split.
  { intros ch b ofs Hb Hr. rewrite (Mem.load_storebytes_other _ _ _ _ _ SG).
    - apply LF, Hb.
    - rewrite HCBL. change (Z.of_nat (Z.to_nat 160)) with 160.
      destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia]. }
  split; [intros b ofs k p Hp; eapply Mem.perm_storebytes_1; [exact SG|apply PF, Hp]|].
  split.
  { intros b Hb. eapply Mem.storebytes_valid_block_1; [exact SG|].
    eapply Mem.store_valid_block_1; [exact SF|]. eapply Mem.store_valid_block_1; [exact SS|].
    unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ SW4).
    eapply Mem.store_valid_block_1; [exact SV|]. eapply Mem.store_valid_block_1; [exact SI|].
    unfold Mem.valid_block. rewrite (store_words_nextblock _ _ _ _ _ SW3), (store_words_nextblock _ _ _ _ _ SW2),
      (store_words_nextblock _ _ _ _ _ SW1). exact Hb. }
  intros t le' mf out HRest. rewrite ci_body_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := le3) (m1 := mG); [|exact HRest].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mF).
  - rewrite ci_fill_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mS).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mW4).
      * eapply (zsr_exec e bCmp _ 112 (fun le m => ev_cin_spk le m) eq_refl ltac:(lia) 8 0%nat ltac:(lia));
          [|exact SW4].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mI).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mW3).
           ++ eapply (zsr_exec e bCmp _ 64 (fun le m => ev_cin_txid le m) eq_refl ltac:(lia) 8 0%nat ltac:(lia));
                [|exact SW3].
              eapply (zsr_exec e bCmp _ 32 (fun le m => ev_cin_field le m _ 32 _ envu_sigInput_scriptSigHash)
                eq_refl ltac:(lia) 8 0%nat ltac:(lia)); [|exact SW2].
              cbn [repeat store_words] in SW1.
              destruct (Mem.store Mint32 m bCmp 0 (Vint Int.zero)) as [m0a|] eqn:S0; [|discriminate].
              eapply (zsr_exec e bCmp _ 0 (fun le m => ev_cin_field le m _ 0 _ envu_sigInput_annexHash)
                eq_refl ltac:(lia) 7 1%nat ltac:(lia)); [|exact SW1].
              eapply (exec_zero_g e bCmp _ 0 (fun le m => ev_cin_field le m _ 0 _ envu_sigInput_annexHash)
                eq_refl ltac:(lia)); [lia|exact S0].
           ++ unfold ci_ix.
              eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mW3).
              ** apply exec_Sset. eapply eval_envu_field_value;
                   [reflexivity|exact envu_rawInput_prevIx|reflexivity|apply eval_envu_deref_struct; exact HlI|].
                 rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
                 rewrite L3 by exact NiC. exact HIx.
              ** eapply exec_Sassign with (v2 := Vint ix) (v := Vlong (Int64.repr (Int.unsigned ix))).
                 --- eapply eval_envu_field_lvalue; [reflexivity|exact envu_outpoint_ix|].
                     apply (ev_cin_field le1 mW3 _ 64 _ envu_sigInput_prevOutpoint).
                 --- apply eval_Etempvar. apply PTree.gss.
                 --- reflexivity.
                 --- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
                     rewrite envu_ptr_add_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
                     rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
                     exact SI.
        -- unfold ci_value.
           eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong Int64.zero).
           ++ eapply eval_envu_field_lvalue; [reflexivity|exact envu_sigOutput_value|].
              apply (ev_cin_field le1 mI _ 104 _ envu_sigInput_txo).
           ++ apply eval_Econst_int.
           ++ reflexivity.
           ++ eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
              rewrite Ptrofs.add_zero.
              rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
              exact SV.
      * unfold ci_sequence.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mW4).
        -- apply exec_Sset. eapply eval_envu_field_value;
             [reflexivity|exact envu_rawInput_sequence|reflexivity|apply eval_envu_deref_struct; exact HlI1|].
           rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
           rewrite L4 by exact NiC. exact HSq.
        -- eapply exec_Sassign with (v2 := Vint sq) (v := Vlong (Int64.repr (Int.unsigned sq))).
           ++ eapply eval_envu_field_lvalue; [reflexivity|exact envu_sigInput_sequence|apply ev_cin].
           ++ apply eval_Etempvar. apply PTree.gss.
           ++ reflexivity.
           ++ eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
              rewrite Ptrofs.add_zero_l.
              rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
              exact SS.
    + unfold ci_hasAnnex.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mS).
      * apply exec_Sset. eapply eval_envu_field_value;
          [reflexivity|exact envu_rawInput_annex|reflexivity|apply eval_envu_deref_struct; exact HlI2|].
        rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
        rewrite Z.add_0_r, LS by exact NiC. exact HAnx.
      * eapply exec_Sassign with (v2 := Vint hasv) (v := Vint hasv).
        -- eapply eval_envu_field_lvalue; [reflexivity|exact envu_sigInput_hasAnnex|apply ev_cin].
        -- destruct HAn as [[-> ->]|(ba & oa & -> & HPn & ->)].
           ++ eapply eval_Eunop with (v1 := Vint Int.one);
                [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity].
           ++ eapply eval_Eunop with (v1 := Vint Int.zero); [|reflexivity].
              eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|].
              assert (HW : Mem.weak_valid_pointer mS ba (Ptrofs.unsigned oa) = true).
              { unfold Mem.weak_valid_pointer. apply orb_true_iff. left.
                apply Mem.valid_pointer_nonempty_perm.
                eapply Mem.perm_store_1; [exact SS|]. apply P4, HPn. }
              cbn. unfold sem_notbool, bool_val. cbn. rewrite HW. reflexivity.
        -- cbn. rewrite ci_bool_cast by exact Hh01. reflexivity.
        -- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
           rewrite Ptrofs.add_zero_l.
           rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
           exact SF.
  - unfold ci_copy.
    eapply exec_Sassign with (v2 := Vptr bCmp Ptrofs.zero) (v := Vptr bCmp Ptrofs.zero).
    + eapply eval_Ederef. apply eval_Etempvar. unfold le3, le2, le1. rewrite !PTree.gso by discriminate. exact HlR.
    + apply ev_cin.
    + reflexivity.
    + eapply assign_loc_copy with (bytes := bytes); cbn [typeof].
      * reflexivity.
      * intros _. rewrite ci_blockcopy_SIN. exists 0. reflexivity.
      * intros _. rewrite ci_blockcopy_SIN, Ptrofs.unsigned_repr by lia. exact HoA.
      * left. exact NCr.
      * rewrite ci_sizeof_SIN. exact HCB.
      * rewrite Ptrofs.unsigned_repr by lia. exact SG.
Qed.
End CopyInputFill.
