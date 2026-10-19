(** [simplicity_bitcoin_mallocTransaction], last part:
      { sha256_context ctx_txHash = sha256_init(tx->txHash.s);
        sha256_u32be(&ctx_txHash, tx->version); sha256_u32be(&ctx_txHash, tx->lockTime);
        sha256_hash(&ctx_txHash, &tx->inputsHash); sha256_hash(&ctx_txHash, &tx->outputsHash);
        sha256_hash(&ctx_txHash, &tx->inputUTXOsHash); sha256_finalize(&ctx_txHash); }
      return tx;
    Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops.
Require Import C.jet_bitcoin_env_ctxs_calls C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_calls.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

(** [mt_rest4 = Ssequence mt_outblock mt_rest5]. *)
Definition mt_outblock : statement :=
  ltac:(let b := eval cbv delta [mt_rest4] in mt_rest4 in lazymatch b with Ssequence ?s _ => exact s end).
Definition mt_rest5 : statement :=
  ltac:(let b := eval cbv delta [mt_rest4] in mt_rest4 in lazymatch b with Ssequence _ ?r => exact r end).
Definition mt_tx_tail : statement :=
  ltac:(let b := eval cbv delta [mt_rest5] in mt_rest5 in
        lazymatch b with Ssequence (Ssequence _ ?t) _ => exact t end).

Lemma mt_rest5_shape bR bC :
  mt_rest5 = Ssequence (inits_stmt [(__res, _ctx_txHash, _txHash, 368, bR, bC)] mt_tx_tail)
               (Sreturn (Some (Etempvar _tx (tptr TX)))).
Proof. reflexivity. Qed.

Lemma envu_tx_txHash : envu_field_at _bitcoinTransaction _txHash 368.
Proof. exact (mt_hash_offsets 11 _txHash eq_refl). Qed.
Lemma envu_tx_inputsHash : envu_field_at _bitcoinTransaction _inputsHash 336.
Proof. exact (mt_hash_offsets 10 _inputsHash eq_refl). Qed.
Lemma envu_tx_outputsHash : envu_field_at _bitcoinTransaction _outputsHash 80.
Proof. exact (mt_hash_offsets 2 _outputsHash eq_refl). Qed.
Lemma envu_tx_inputUTXOsHash : envu_field_at _bitcoinTransaction _inputUTXOsHash 208.
Proof. exact (mt_hash_offsets 6 _inputUTXOsHash eq_refl). Qed.

(** The SHA-256 state written to [tx->txHash]. *)
Definition mt_txhash_regs (v lt : int64) (I O U : list int) : list int :=
  let s1 := absorb_i [] sha256_iv_words (c_be32_bytes v) in
  let s2 := absorb_i (fst s1) (snd s1) (c_be32_bytes lt) in
  let s3 := absorb_i (fst s2) (snd s2) (be_bytes (norm8 I)) in
  let s4 := absorb_i (fst s3) (snd s3) (be_bytes (norm8 O)) in
  let s5 := absorb_i (fst s4) (snd s4) (be_bytes (norm8 U)) in
  snd (absorb_i (fst s5) (snd s5)
    (sha_pad (Int64.add (Int64.add (Int64.add (Int64.add (Int64.add Int64.zero (Int64.repr 4)) (Int64.repr 4))
       (Int64.repr 32)) (Int64.repr 32)) (Int64.repr 32)))).

Local Opaque sha_ge.

Lemma ev_tx_field e le m bA f delta ty chunk v :
  le!_tx = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTransaction f delta ->
  access_mode ty = By_value chunk -> 0 <= delta <= 4000 ->
  Mem.load chunk m bA delta = Some v ->
  eval_expr sha_ge e le m (Efield TXD f ty) v.
Proof.
  intros Hle Hf Hacc Hd HL.
  eapply eval_envu_field_value; [reflexivity|exact Hf|exact Hacc|apply eval_envu_deref_struct; exact Hle|].
  unfold Mem.loadv. rewrite mt_off by exact Hd. exact HL.
Qed.

Section TxHash.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bR bC : block) (v lt : int64) (I O U : list int).
Hypothesis HeI : e!_sha256_init = None.
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU : e!_sha256_u32be = None.
Hypothesis HeF : e!_sha256_finalize = None.
Hypothesis NGA : GC <> bA.
Hypothesis NMA : GM <> bA.
Hypothesis HOk : item_ok e bA (__res, _ctx_txHash, _txHash, 368, bR, bC).

Lemma tx_sep1 l regs c ovf : ctxs_sep bA [(bC, 368, l, regs, c, ovf)].
Proof.
  destruct HOk as (_ & _ & _ & _ & _ & NAC & _ & _ & NGC & NMC & _).
  split; [exact NGA|]. split; [exact NMA|]. split.
  - intros k c0 Hk. destruct k as [|k]; cbn in Hk; [injection Hk as <-|destruct k; discriminate].
    cbn [ctx_block ctx_out]. repeat split; auto; try lia.
    change Ptrofs.max_unsigned with 18446744073709551615. lia.
  - intros i j ci cj Hi Hj Hij. destruct i as [|i]; destruct j as [|j]; try congruence;
      cbn in Hi, Hj; try (destruct i; discriminate); destruct j; discriminate.
Qed.

Theorem mt_txhash le m :
  le!_tx = Some (Vptr bA Ptrofs.zero) ->
  item_perms bA m (__res, _ctx_txHash, _txHash, 368, bR, bC) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  Mem.load Mint64 m bA 464 = Some (Vlong v) -> Mem.load Mint64 m bA 472 = Some (Vlong lt) ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (336 + 4 * Z.of_nat j) = Some (Vint (nth j I Int.zero))) ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (80 + 4 * Z.of_nat j) = Some (Vint (nth j O Int.zero))) ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bA (208 + 4 * Z.of_nat j) = Some (Vint (nth j U Int.zero))) ->
  exists m' le',
    Clight2.exec_stmt sha_ge e le m mt_rest5 E0 le' m' (Out_return (Some (Vptr bA Ptrofs.zero, tptr TX))) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bA (368 + 4 * Z.of_nat j) = Some (Vint (nth j (mt_txhash_regs v lt I O U) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bR -> b <> bC ->
       (b <> bA \/ ofs + size_chunk ch <= 368 \/ 400 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hle HPerm Hdisp HMax HV HLt HI HO HU.
  pose proof HOk as (HeR & HeC & _ & _ & _ & NAC & NAR & NRC & NGC & NMC & NGR & NMR).
  assert (VA : Mem.valid_block m bA) by (eapply load_valid_block; exact HV).
  destruct (inits_exec e bA HeI NGA NMA [(__res, _ctx_txHash, _txHash, 368, bR, bC)] [] le m)
    as (m1 & HCs1 & HL1 & HP1 & HV1 & HK1); try assumption.
  { cbn [items_wf]. split; [exact HOk|]. split; [intros c []|exact Logic.I]. }
  { intros it [<-|[]]. exact HPerm. }
  { constructor. }
  cbn [map rev app item_entry] in HCs1.
  assert (K1 : forall ch ofs, (ofs + size_chunk ch <= 368 \/ 400 <= ofs) ->
    Mem.load ch m1 bA ofs = Mem.load ch m bA ofs).
  { intros ch ofs Hr. apply HL1; [exact VA|]. intros it [<-|[]]. cbn [item_untouched].
    split; [exact NAR|]. split; [exact NAC|]. right. lia. }
  set (live := fun _ : nat => True).
  pose proof (ctxs_live_all m1 bA _ HCs1) as HC1. fold live in HC1.
  (* version, lock time *)
  destruct (live_u32be Hmodel bA _ live 0%nat bC 368 [] sha256_iv_words Int64.zero false
    (tx_sep1 _ _ _ _) eq_refl Logic.I m1 v HC1) as (m2 & vr2 & HCall2 & HC2 & HL2 & HP2 & HV2).
  cbn [upd] in HC2.
  destruct (live_u32be Hmodel bA _ live 0%nat bC 368 _ _ _ _
    (tx_sep1 _ _ _ _) eq_refl Logic.I m2 lt HC2) as (m3 & vr3 & HCall3 & HC3 & HL3 & HP3 & HV3).
  cbn [upd] in HC3.
  assert (VA1 : Mem.valid_block m1 bA) by (apply HV1, VA).
  assert (K3 : forall ch ofs, (ofs + size_chunk ch <= 368 \/ 400 <= ofs) ->
    Mem.load ch m3 bA ofs = Mem.load ch m bA ofs).
  { intros ch ofs Hr. rewrite HL3; [|apply HV2, VA1|exact NAC|right; lia].
    rewrite HL2; [|exact VA1|exact NAC|right; lia]. apply K1, Hr. }
  set (oI := Ptrofs.repr 336). set (oO := Ptrofs.repr 80). set (oU := Ptrofs.repr 208).
  assert (Hn8 : forall R, length (norm8 R) = 8%nat) by reflexivity.
  (* the three hashes *)
  destruct (live_hash Hmodel bA _ live 0%nat bC 368 _ _ _ _ (tx_sep1 _ _ _ _) eq_refl Logic.I m3 bA oI (norm8 I) HC3 (Hn8 I))
    as (m4 & HCall4 & HC4 & HL4 & HP4 & HV4).
  { change (Ptrofs.unsigned oI) with 336. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. change (Ptrofs.unsigned oI) with 336. rewrite norm8_nth by exact Hj.
    rewrite K3 by (left; change (size_chunk Mint32) with 4; lia). apply HI, Hj. }
  cbn [upd] in HC4.
  assert (VA3 : Mem.valid_block m3 bA) by (apply HV3, HV2, VA1).
  destruct (live_hash Hmodel bA _ live 0%nat bC 368 _ _ _ _ (tx_sep1 _ _ _ _) eq_refl Logic.I m4 bA oO (norm8 O) HC4 (Hn8 O))
    as (m5 & HCall5 & HC5 & HL5 & HP5 & HV5).
  { change (Ptrofs.unsigned oO) with 80. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. change (Ptrofs.unsigned oO) with 80. rewrite norm8_nth by exact Hj.
    rewrite HL4; [|exact VA3|exact NAC|right; left; change (size_chunk Mint32) with 4; lia].
    rewrite K3 by (left; change (size_chunk Mint32) with 4; lia). apply HO, Hj. }
  cbn [upd] in HC5.
  destruct (live_hash Hmodel bA _ live 0%nat bC 368 _ _ _ _ (tx_sep1 _ _ _ _) eq_refl Logic.I m5 bA oU (norm8 U) HC5 (Hn8 U))
    as (m6 & HCall6 & HC6 & HL6 & HP6 & HV6).
  { change (Ptrofs.unsigned oU) with 208. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. change (Ptrofs.unsigned oU) with 208. rewrite norm8_nth by exact Hj.
    rewrite HL5; [|apply HV4, VA3|exact NAC|right; left; change (size_chunk Mint32) with 4; lia].
    rewrite HL4; [|exact VA3|exact NAC|right; left; change (size_chunk Mint32) with 4; lia].
    rewrite K3 by (left; change (size_chunk Mint32) with 4; lia). apply HU, Hj. }
  cbn [upd] in HC6.
  destruct (live_finalize Hmodel bA _ live 0%nat bC 368 _ _ _ _ (tx_sep1 _ _ _ _) eq_refl Logic.I m6 HC6)
    as (m7 & vr7 & HCall7 & HReg7 & _ & HL7 & HP7 & HV7).
  fold (mt_txhash_regs v lt I O U) in HReg7.
  set (le3 := PTree.set _t'3 (Vlong v) le).
  set (le2 := PTree.set _t'2 (Vlong lt) le3).
  assert (Hle3 : le3!_tx = Some (Vptr bA Ptrofs.zero)) by (unfold le3; rewrite PTree.gso by discriminate; exact Hle).
  assert (Hle2 : le2!_tx = Some (Vptr bA Ptrofs.zero)) by (unfold le2; rewrite PTree.gso by discriminate; exact Hle3).
  exists m7, le2. split; [|split; [|split; [|split]]].
  - rewrite (mt_rest5_shape bR bC).
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m7).
    + apply HK1. cbv delta [mt_tx_tail] beta iota.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m2).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m1).
        - apply exec_Sset. eapply ev_tx_field with (delta := 464) (chunk := Mint64);
            [exact Hle|exact envu_tx_version|reflexivity|lia|].
          rewrite K1 by (right; lia). exact HV.
        - eapply mt_call_u32be with (bx := bC) (x := v);
            [exact HeU|exact HeC|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
        - apply exec_Sset. eapply ev_tx_field with (delta := 472) (chunk := Mint64);
            [exact Hle3|exact envu_tx_lockTime|reflexivity|lia|].
          rewrite HL2; [|exact VA1|exact NAC|right; right; lia]. rewrite K1 by (right; lia). exact HLt.
        - eapply mt_call_u32be with (bx := bC) (x := lt);
            [exact HeU|exact HeC|apply eval_Etempvar; apply PTree.gss|reflexivity|exact HCall3]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
      { eapply mt_call_hash with (bx := bC) (bt := bA) (ot := oI);
          [exact HeH|exact HeC|apply ev_tx_mid_addr; [exact Hle2|exact envu_tx_inputsHash]|reflexivity|exact HCall4]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m5).
      { eapply mt_call_hash with (bx := bC) (bt := bA) (ot := oO);
          [exact HeH|exact HeC|apply ev_tx_mid_addr; [exact Hle2|exact envu_tx_outputsHash]|reflexivity|exact HCall5]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m6).
      { eapply mt_call_hash with (bx := bC) (bt := bA) (ot := oU);
          [exact HeH|exact HeC|apply ev_tx_mid_addr; [exact Hle2|exact envu_tx_inputUTXOsHash]|reflexivity|exact HCall6]. }
      eapply mt_call_finalize; [exact HeF|exact HeC|exact HCall7].
    + apply exec_Sreturn_some. apply eval_Etempvar. exact Hle2.
  - intros j Hj. apply HReg7, Hj.
  - intros ch b ofs Hb H1 H2 Hr.
    assert (Vb1 : Mem.valid_block m1 b) by (apply HV1, Hb).
    rewrite HL7; [|apply HV6, HV5, HV4, HV3, HV2, Vb1|exact H2|exact Hr].
    rewrite HL6; [|apply HV5, HV4, HV3, HV2, Vb1|exact H2|exact Hr].
    rewrite HL5; [|apply HV4, HV3, HV2, Vb1|exact H2|exact Hr].
    rewrite HL4; [|apply HV3, HV2, Vb1|exact H2|exact Hr].
    rewrite HL3; [|apply HV2, Vb1|exact H2|exact Hr].
    rewrite HL2; [|exact Vb1|exact H2|exact Hr].
    apply HL1; [exact Hb|]. intros it [<-|[]]. cbn [item_untouched]. repeat split; assumption.
  - intros b ofs k p Hp.
    assert (Hp1 : Mem.perm m1 b ofs k p) by (apply HP1, Hp).
    assert (Hp2 : Mem.perm m2 b ofs k p) by (apply HP2; [eapply Mem.perm_valid_block; exact Hp1|exact Hp1]).
    assert (Hp3 : Mem.perm m3 b ofs k p) by (apply HP3; [eapply Mem.perm_valid_block; exact Hp2|exact Hp2]).
    assert (Hp4 : Mem.perm m4 b ofs k p) by (apply HP4; [eapply Mem.perm_valid_block; exact Hp3|exact Hp3]).
    assert (Hp5 : Mem.perm m5 b ofs k p) by (apply HP5; [eapply Mem.perm_valid_block; exact Hp4|exact Hp4]).
    assert (Hp6 : Mem.perm m6 b ofs k p) by (apply HP6; [eapply Mem.perm_valid_block; exact Hp5|exact Hp5]).
    apply HP7; [eapply Mem.perm_valid_block; exact Hp6|exact Hp6].
  - intros b Hb. apply HV7, HV6, HV5, HV4, HV3, HV2, HV1, Hb.
Qed.
End TxHash.
