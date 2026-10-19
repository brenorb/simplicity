(** [simplicity_bitcoin_mallocTransaction], the input loop
      for (i = 0; i < tx->numInputs; ++i) {
        copyInput(&input[i], &rawTx->input[i]);
        tx->totalInputValue += input[i].txo.value;
        if (input[i].sequence < 0xffffffff) { tx->isFinal = false; }
        ... the context operations ([in_ops]) ... }
    for any number of inputs.  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls C.jet_bitcoin_env_ctxs_core.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inops.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma sha_copyInput_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _copyInput = Some (sha_symbol_block _copyInput).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_copyInput_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _copyInput) Ptrofs.zero) =
    Some (Internal f_copyInput).
Proof. vm_compute; reflexivity. Qed.
Lemma envu_rawTx_input : envu_field_at _rawBitcoinTransaction _input 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma mt_sizeof_RIN_Z : sizeof sha_ge RIN = 64.
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma ci_call_copyInput e le m m' (a1 a2 : expr) b1 o1 b2 o2 :
  e!_copyInput = None ->
  eval_expr sha_ge e le m a1 (Vptr b1 o1) -> typeof a1 = tptr SIN ->
  eval_expr sha_ge e le m a2 (Vptr b2 o2) -> typeof a2 = tptr RIN ->
  Clight2.eval_funcall sha_ge m (Internal f_copyInput) [Vptr b1 o1; Vptr b2 o2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _copyInput (Tfunction (Tcons (tptr SIN) (Tcons (tptr RIN) Tnil)) tvoid cc_default))
       [a1; a2]) E0 le m' Out_normal.
Proof.
  intros He H1 T1 H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _copyInput) Ptrofs.zero)
    (vargs := [Vptr b1 o1; Vptr b2 o2]) (f := Internal f_copyInput).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_copyInput_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|rewrite T1; reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_copyInput_funct.
  - reflexivity.
  - exact HC.
Qed.

Section InLoop.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bI bG bN bQ bU bS bV bP braw bri : block) (oraw ori ni : Z).
Variables (data : nat -> in_data) (oldb : block -> Prop) (m0 : mem).

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let Nn := Z.to_nat ni.
Let blocks := [bI; bG; bN; bQ; bU; bS; bV; bP].
Local Notation allL := (fun _ : nat => True).
Local Notation cores := (in_cores data bI bG bN bQ bU bS bV bP).

Hypothesis HeP : e!_ctx_inputOutpointsHash = Some (bP, CTX).
Hypothesis HeV : e!_ctx_inputValuesHash = Some (bV, CTX).
Hypothesis HeS : e!_ctx_inputScriptsHash = Some (bS, CTX).
Hypothesis HeQ : e!_ctx_inputSequencesHash = Some (bQ, CTX).
Hypothesis HeN : e!_ctx_inputAnnexesHash = Some (bN, CTX).
Hypothesis HeG : e!_ctx_inputScriptSigsHash = Some (bG, CTX).
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU4 : e!_sha256_u32be = None.
Hypothesis HeU8 : e!_sha256_u64be = None.
Hypothesis HeUc : e!_sha256_uchar = None.
Hypothesis HeCp : e!_copyInput = None.
Hypothesis Hni : 0 <= ni <= 4294967295.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis Hori : 0 <= ori /\ ori + 64 * ni <= Ptrofs.max_unsigned.
Hypothesis HNA : ~ In bA blocks.
Hypothesis Hold : forall b, oldb b -> Mem.valid_block m0 b /\ b <> bA /\ ~ In b blocks.
Hypothesis HoRaw : oldb braw.
Hypothesis HoRi0 : 0 < ni -> oldb bri.
Hypothesis HRi0 : 0 < ni -> Mem.load Mptr m0 braw (oraw + 8) = Some (Vptr bri (Ptrofs.repr ori)).
Hypothesis HRaw : forall j, (j < Nn)%nat -> raw_in_at oldb m0 bri (ori + 64 * Z.of_nat j) (data j).
Hypothesis PA0 : Mem.range_perm m0 bA 0 (488 + 160 * ni) Cur Writable.
Hypothesis HNi0 : Mem.load Mint64 m0 bA 448 = Some (Vlong (Int64.repr ni)).

Definition in_inv (k : nat) (le : temp_env) (m : mem) : Prop :=
  le!_i = Some (Vlong (Int64.repr (Z.of_nat k))) /\
  le!_tx = Some (Vptr bA Ptrofs.zero) /\
  le!_input = Some (Vptr bA (Ptrofs.repr 488)) /\
  le!_rawTx = Some rawv /\
  le!_output = Some (Vptr bA (Ptrofs.repr (488 + 160 * ni))) /\
  LS m bA (cores k) allL /\
  Mem.load Mint64 m bA 432 = Some (Vlong (in_tot data k)) /\
  Mem.load Mint8unsigned m bA 480 = Some (Vint (in_final data k)) /\
  (forall j, (j < k)%nat -> in_rec m bA (488 + 160 * Z.of_nat j) (data j)) /\
  (forall ch b ofs, oldb b -> Mem.load ch m b ofs = Mem.load ch m0 b ofs) /\
  (forall ch ofs,
     (ofs + size_chunk ch <= 112 \/ (368 <= ofs /\ ofs + size_chunk ch <= 432) \/
      (440 <= ofs /\ ofs + size_chunk ch <= 480)) ->
     Mem.load ch m bA ofs = Mem.load ch m0 bA ofs) /\
  (forall b ofs kk p, Mem.perm m0 b ofs kk p -> Mem.perm m b ofs kk p) /\
  (forall b, Mem.valid_block m0 b -> Mem.valid_block m b).

Lemma in_NnN : Z.of_nat Nn = ni.
Proof. unfold Nn. apply Z2Nat.id. lia. Qed.

Lemma in_numInputs le m :
  le!_tx = Some (Vptr bA Ptrofs.zero) ->
  (forall ch ofs,
     (ofs + size_chunk ch <= 112 \/ (368 <= ofs /\ ofs + size_chunk ch <= 432) \/
      (440 <= ofs /\ ofs + size_chunk ch <= 480)) ->
     Mem.load ch m bA ofs = Mem.load ch m0 bA ofs) ->
  eval_expr sha_ge e le m (Efield TXD _numInputs tulong) (Vlong (Int64.repr ni)).
Proof.
  intros Hle HF.
  eapply ev_tx_field with (delta := 448) (chunk := Mint64); [exact Hle|exact envu_tx_numInputs|reflexivity|lia|].
  rewrite HF; [exact HNi0|right; right; change (size_chunk Mint64) with 8; lia].
Qed.

Lemma in_exit le m : in_inv Nn le m ->
  exists le', in_inv Nn le' m /\
    Clight2.exec_stmt sha_ge e le m (Sloop mt_in_s1 mt_in_s2) E0 le' m Out_normal.
Proof.
  intros (Hi & Htx & Hin & Hraw & Hout & HLS & HT & HFi & HR & HFo & HFa & HPm & HV).
  exists (PTree.set _t'17 (Vlong (Int64.repr ni)) le). split.
  { unfold in_inv. rewrite !PTree.gso by discriminate. repeat (split; [assumption|]). assumption. }
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  cbv delta [mt_in_s1] beta iota.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'17 (Vlong (Int64.repr ni)) le) (m1 := m).
  - apply exec_Sset. apply in_numInputs; assumption.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hi
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat Nn)) (Int64.repr ni))) = Some (Vint Int.zero)).
      rewrite in_NnN, i64_ltu_repr by lia. rewrite zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma in_step k le m : (k < Nn)%nat -> in_inv k le m ->
  exists le1 m1 le' m',
    in_inv (S k) le' m' /\
    Clight2.exec_stmt sha_ge e le m mt_in_s1 E0 le1 m1 Out_normal /\
    Clight2.exec_stmt sha_ge e le1 m1 mt_in_s2 E0 le' m' Out_normal.
Proof.
  intros Hk (Hi & Htx & Hin & Hraw & Hout & HLS & HT & HFi & HR & HFo & HFa & HPm & HV).
  pose proof in_NnN as HNn.
  assert (Hpos : 0 < ni) by (clear - Hk HNn; lia).
  pose proof (HoRi0 Hpos) as HoRi. pose proof (HRi0 Hpos) as HRi.
  set (kz := Z.of_nat k) in *.
  assert (Hkz : 0 <= kz < ni) by (unfold kz; flia).
  set (X := 488 + 160 * kz).
  assert (HXb : 488 <= X /\ X + 160 <= 488 + 160 * ni /\ X + 160 <= Ptrofs.max_unsigned).
  { unfold X. change Ptrofs.max_unsigned with 18446744073709551615. flia. }
  set (d := data k).
  set (sq64 := Int64.repr (Int.unsigned (d_sq d))).
  destruct (Hold braw HoRaw) as (Vraw & NrA & Nrb).
  destruct (Hold bri HoRi) as (Vri & NiA & Nib).
  pose proof (raw_in_frame oldb m0 m bri (ori + 64 * kz) d (HRaw k Hk) HoRi HFo HV) as HRawM.
  destruct HRawM as (A1 & A2 & A3 & O3 & A4 & A5 & A6 & A7 & O7 & A8 & O8 & A9 & A10).
  unfold in_cores, mk_core in HLS.
  let cc := ls_cores HLS in
  destruct (LS_facts bA cc allL 0%nat _ _ _ _ _ eq_refl Logic.I m HLS) as (NG & NM & _ & _ & VA & Hdisp & HMax).
  assert (HAn : annex_spec bA m (d_vannex d) (d_has d) (d_areg d)).
  { destruct A2 as [A2|(bax & oax & bad & oad & abs & E1 & E2 & E3 & E4 & Oa & Od & HB)]; [left; exact A2|right].
    exists bax, oax, bad, oad, abs.
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    split; [exact (proj1 (proj2 (Hold _ Oa)))|]. split; [exact (proj1 (proj2 (Hold _ Od)))|exact HB]. }
  (* copyInput(&input[i], &rawTx->input[i]) *)
  assert (Q1 : 0 <= X /\ X + 160 <= Ptrofs.max_unsigned) by flia.
  assert (Q2 : (8 | X)) by (unfold X; exists (61 + 20 * kz); flia).
  assert (Q3 : 0 <= ori + 64 * kz /\ ori + 64 * kz + 64 <= Ptrofs.max_unsigned) by flia.
  assert (Q4 : Mem.range_perm m bA X (X + 160) Cur Writable).
  { intros o Ho. apply HPm, PA0. flia. }
  destruct (eval_copyInput Hmodel bA bri X (ori + 64 * kz) Q1 Q2 Q3 (not_eq_sym NG) (not_eq_sym NM) NiA m
              (d_vannex d) (d_has d) (d_areg d) (d_btx d) (d_otx d) (d_txb d) (d_val d)
              (d_bsp d) (d_osp d) (d_spb d) (d_bss d) (d_oss d) (d_ssb d) (d_ix d) (d_sq d)
              Q4 A1 HAn A3 (proj1 (proj2 (Hold _ O3))) A4 A5 A6 A7 (proj1 (proj2 (Hold _ O7)))
              A8 (proj1 (proj2 (Hold _ O8))) A9 A10 Hdisp HMax)
    as (m1 & HCall1 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & HL1 & HP1 & HV1).
  assert (HRec1 : in_rec m1 bA X d).
  { unfold in_rec. repeat (split; [assumption|]). assumption. }
  assert (HOuts : forall lo hi, 368 <= lo -> forall j cj,
    nth_error [(bI, 336, fst st0, snd st0, Int64.zero);
               (bG, 304, fst (in_stSS data k), snd (in_stSS data k), in_cnt 32 k);
               (bN, 272, fst (in_stAn data k), snd (in_stAn data k), in_nAn data k);
               (bQ, 240, fst (in_stSeq data k), snd (in_stSeq data k), in_cnt 4 k);
               (bU, 208, fst st0, snd st0, Int64.zero);
               (bS, 176, fst (in_stSc data k), snd (in_stSc data k), in_cnt 32 k);
               (bV, 144, fst (in_stV data k), snd (in_stV data k), in_cnt 8 k);
               (bP, 112, fst (in_stOP data k), snd (in_stOP data k), in_cntOP k)] j = Some cj ->
    allL j -> core_out cj + 32 <= lo \/ hi <= core_out cj).
  { intros lo hi Hlo j cj Hj _. left.
    do 8 (destruct j as [|j]; cbn [nth_error] in Hj; [injection Hj as <-; cbn [core_out]; clear - Hlo; lia|]).
    destruct j; discriminate. }
  let cc := ls_cores HLS in assert (HLS1 : LS m1 bA cc allL).
  { eapply (LS_other m m1 bA _ allL X (X + 160) HLS); [apply HOuts; flia|exact HL1|exact HP1]. }
  (* tx->totalInputValue += input[i].txo.value *)
  assert (HT1 : Mem.load Mint64 m1 bA 432 = Some (Vlong (in_tot data k))).
  { rewrite HL1; [exact HT|exact VA|right; left; change (size_chunk Mint64) with 8; flia]. }
  destruct (Mem.valid_access_store m1 Mint64 bA 432 (Vlong (Int64.add (in_tot data k) (d_val d)))) as [m2 SS].
  { split; [|exists 54; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    apply HP1, HPm, PA0. flia. }
  assert (HL2 : forall ch b ofs, (b <> bA \/ ofs + size_chunk ch <= 432 \/ 440 <= ofs) ->
    Mem.load ch m2 b ofs = Mem.load ch m1 b ofs).
  { intros ch b ofs Hr. eapply Mem.load_store_other; [exact SS|].
    destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; change (size_chunk Mint64) with 8; flia]. }
  assert (HP2 : forall b ofs kk p, Mem.perm m1 b ofs kk p -> Mem.perm m2 b ofs kk p).
  { intros b ofs kk p Hp. eapply Mem.perm_store_1; [exact SS|exact Hp]. }
  assert (HV2 : forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact SS|exact Hb]. }
  let cc := ls_cores HLS in assert (HLS2 : LS m2 bA cc allL).
  { eapply (LS_other m1 m2 bA _ allL 432 440 HLS1); [apply HOuts; flia|intros ch b ofs _ Hr; apply HL2, Hr|exact HP2]. }
  (* if (input[i].sequence < 0xffffffff) { tx->isFinal = false; } *)
  set (leA := PTree.set _t'17 (Vlong (Int64.repr ni)) le).
  set (leB := PTree.set _t'16 (Vptr bri (Ptrofs.repr ori)) leA).
  set (leC := PTree.set _t'14 (Vlong (in_tot data k)) leB).
  set (leD := PTree.set _t'15 (Vlong (d_val d)) leC).
  set (leE := PTree.set _t'13 (Vlong sq64) leD).
  assert (GE : forall x, x <> _t'17 -> x <> _t'16 -> x <> _t'14 -> x <> _t'15 -> x <> _t'13 -> leE!x = le!x).
  { intros x H7 H6 H4 H5 H3. unfold leE, leD, leC, leB, leA. rewrite !PTree.gso by assumption. reflexivity. }
  assert (HtxE : leE!_tx = Some (Vptr bA Ptrofs.zero)) by (rewrite GE by discriminate; exact Htx).
  assert (HF2 : Mem.load Mint8unsigned m2 bA 480 = Some (Vint (in_final data k))).
  { rewrite HL2 by (right; right; flia).
    rewrite HL1; [exact HFi|exact VA|right; left; change (size_chunk Mint8unsigned) with 1; flia]. }
  assert (HIf : exists m3,
    Clight2.exec_stmt sha_ge e leE m2
      (Sifthenelse (Ebinop Olt (Etempvar _t'13 tulong) (Econst_int (Int.repr (-1)) tuint) tint)
         (Sassign (Efield TXD _isFinal tbool) (Econst_int (Int.repr 0) tint)) Sskip) E0 leE m3 Out_normal /\
    Mem.load Mint8unsigned m3 bA 480 = Some (Vint (in_final data (S k))) /\
    (forall ch b ofs, (b <> bA \/ ofs + size_chunk ch <= 480 \/ 481 <= ofs) ->
       Mem.load ch m3 b ofs = Mem.load ch m2 b ofs) /\
    (forall b ofs kk p, Mem.perm m2 b ofs kk p -> Mem.perm m3 b ofs kk p) /\
    (forall b, Mem.valid_block m2 b -> Mem.valid_block m3 b)).
  { cbn [in_final]. fold d. fold sq64.
    destruct (Int64.ltu sq64 (Int64.repr 4294967295)) eqn:Eq.
    - destruct (Mem.valid_access_store m2 Mint8unsigned bA 480 (Vint Int.zero)) as [m3 S3].
      { split; [|exists 480; reflexivity]. intros o Ho. change (size_chunk Mint8unsigned) with 1 in Ho.
        apply HP2, HP1, HPm, PA0. flia. }
      exists m3. split; [|split; [|split; [|split]]].
      + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        * eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
          change (Some (Val.of_bool (Int64.ltu sq64 (Int64.repr 4294967295))) = Some (Vint Int.one)).
          rewrite Eq. reflexivity.
        * reflexivity.
        * eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vint Int.zero).
          -- eapply eval_envu_field_lvalue; [reflexivity|exact envu_tx_isFinal|].
             apply eval_envu_deref_struct. exact HtxE.
          -- apply eval_Econst_int.
          -- reflexivity.
          -- eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by flia. exact S3.
      + rewrite (Mem.load_store_same _ _ _ _ _ _ S3). reflexivity.
      + intros ch b ofs Hr. eapply Mem.load_store_other; [exact S3|].
        destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr
                                     |right; right; change (size_chunk Mint8unsigned) with 1; flia].
      + intros b ofs kk p Hp. eapply Mem.perm_store_1; [exact S3|exact Hp].
      + intros b Hb. eapply Mem.store_valid_block_1; [exact S3|exact Hb].
    - exists m2. split; [|split; [exact HF2|split; [reflexivity|split; auto]]].
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
        change (Some (Val.of_bool (Int64.ltu sq64 (Int64.repr 4294967295))) = Some (Vint Int.zero)).
        rewrite Eq. reflexivity.
      + reflexivity.
      + apply exec_Sskip. }
  destruct HIf as (m3 & HExec3 & HF3 & HL3 & HP3 & HV3).
  let cc := ls_cores HLS in assert (HLS3 : LS m3 bA cc allL).
  { eapply (LS_other m2 m3 bA _ allL 480 481 HLS2); [apply HOuts; flia|intros ch b ofs _ Hr; apply HL3, Hr|exact HP3]. }
  assert (HRec3 : in_rec m3 bA X d).
  { eapply in_rec_frame; [exact HRec1|]. intros ch ofs H1 H2.
    rewrite HL3 by (right; right; flia). apply HL2. right; right; flia. }
  (* the context operations *)
  assert (HinE : leE!_input = Some (Vptr bA (Ptrofs.repr 488))) by (rewrite GE by discriminate; exact Hin).
  assert (HiE : leE!_i = Some (Vlong (Int64.repr kz))) by (rewrite GE by discriminate; exact Hi).
  destruct (in_ops Hmodel e bA bI bG bN bQ bU bS bV bP data k HeP HeV HeS HeQ HeN HeG HeH HeU4 HeU8 HeUc
              ltac:(fold kz; flia) leE m3 HinE HiE HLS3 HRec3)
    as (leF & m4 & HExec4 & GF & HLS4 & (L4 & P4 & V4)).
  fold blocks in L4.
  set (le6 := PTree.set _i (Vlong (Int64.repr (Z.of_nat (S k)))) leF).
  assert (GF' : forall x, x <> _t'9 -> x <> _t'10 -> x <> _t'11 -> x <> _t'12 ->
    x <> _t'17 -> x <> _t'16 -> x <> _t'14 -> x <> _t'15 -> x <> _t'13 -> leF!x = le!x).
  { intros x H9 H10 H11 H12 H7 H6 H4 H5 H3. rewrite GF by assumption. apply GE; assumption. }
  assert (VA3 : Mem.valid_block m3 bA) by (apply HV3, HV2, HV1, VA).
  assert (L4A : forall ch ofs, (ofs + size_chunk ch <= 112 \/ 368 <= ofs) ->
    Mem.load ch m4 bA ofs = Mem.load ch m3 bA ofs).
  { intros ch ofs Hr. apply L4; [exact VA3|]. split; [exact HNA|right; exact Hr]. }
  assert (EvD : forall lx mx, lx!_input = Some (Vptr bA (Ptrofs.repr 488)) -> lx!_i = Some (Vlong (Int64.repr kz)) ->
    eval_expr sha_ge e lx mx DIN (Vptr bA (Ptrofs.repr X))).
  { intros lx mx H1 H2. eapply eval_Elvalue; [eapply eval_Ederef|apply deref_loc_copy; reflexivity].
    eapply eval_Ebinop; [apply eval_Etempvar; exact H1|apply eval_Etempvar; exact H2|].
    unfold X. rewrite <- (ptr_index_long 488 160 kz) by flia. rewrite <- ci_sizeof_SIN. reflexivity. }
  exists leF, m4, le6, m4. split; [|split].
  - unfold in_inv. split; [apply PTree.gss|].
    unfold le6. rewrite !PTree.gso by discriminate.
    split; [rewrite GF' by discriminate; exact Htx|].
    split; [rewrite GF' by discriminate; exact Hin|].
    split; [rewrite GF' by discriminate; exact Hraw|].
    split; [rewrite GF' by discriminate; exact Hout|].
    split; [exact HLS4|].
    split.
    { cbn [in_tot]. rewrite L4A by (right; flia). rewrite HL3 by (right; left; change (size_chunk Mint64) with 8; flia).
      rewrite (Mem.load_store_same _ _ _ _ _ _ SS). reflexivity. }
    split; [rewrite L4A by (right; flia); exact HF3|].
    split.
    { intros j Hj. destruct (Nat.eq_dec j k) as [->|Hne].
      - fold kz. fold X. eapply in_rec_frame; [exact HRec3|]. intros ch ofs H1 H2. apply L4A. right; flia.
      - assert (Hjk : (j < k)%nat) by (clear - Hj Hne; lia).
        eapply in_rec_frame; [exact (HR j Hjk)|]. intros ch ofs H1 H2.
        rewrite L4A by (right; flia). rewrite HL3 by (right; right; flia). rewrite HL2 by (right; right; flia).
        apply HL1; [exact VA|right; left; unfold X, kz; flia]. }
    split.
    { intros ch b ofs Hb. destruct (Hold b Hb) as (Vb & NbA & Nbb).
      assert (Vb1 : Mem.valid_block m1 b) by (apply HV1, HV, Vb).
      rewrite L4; [|apply HV3, HV2, Vb1|split; [exact Nbb|left; exact NbA]].
      rewrite HL3 by (left; exact NbA). rewrite HL2 by (left; exact NbA).
      rewrite HL1; [apply HFo, Hb|apply HV, Vb|left; exact NbA]. }
    split.
    { intros ch ofs Hz. rewrite L4A by flia. rewrite HL3 by (right; left; flia).
      rewrite HL2 by (right; flia). rewrite HL1; [apply HFa, Hz|exact VA|right; left; flia]. }
    split.
    { intros b ofs kk p Hp. apply P4, HP3, HP2, HP1, HPm, Hp. }
    { intros b Hb. apply V4, HV3, HV2, HV1, HV, Hb. }
  - cbv delta [mt_in_s1] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
      - apply exec_Sset. apply in_numInputs; assumption.
      - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        + eapply eval_Ebinop; [apply eval_Etempvar; unfold leA; rewrite PTree.gso by discriminate; exact Hi
                              |apply eval_Etempvar; apply PTree.gss|].
          change (Some (Val.of_bool (Int64.ltu (Int64.repr kz) (Int64.repr ni))) = Some (Vint Int.one)).
          rewrite i64_ltu_repr by flia. rewrite zlt_true by flia. reflexivity.
        + reflexivity.
        + apply exec_Sskip. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leB) (m1 := m1).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leB) (m1 := m).
      - apply exec_Sset. eapply eval_envu_field_value;
          [reflexivity|exact envu_rawTx_input|reflexivity
          |apply eval_envu_deref_struct; unfold leA; rewrite PTree.gso by discriminate; exact Hraw|].
        unfold rawv. rewrite envu_ptr_add_repr by flia. apply envu_loadv_repr; [flia|].
        rewrite HFo by exact HoRaw. exact HRi.
      - eapply ci_call_copyInput with (b1 := bA) (o1 := Ptrofs.repr X) (b2 := bri) (o2 := Ptrofs.repr (ori + 64 * kz));
          [exact HeCp| |reflexivity| |reflexivity|exact HCall1].
        + eapply eval_Ebinop; [apply eval_Etempvar; unfold leB, leA; rewrite !PTree.gso by discriminate; exact Hin
                              |apply eval_Etempvar; unfold leB, leA; rewrite !PTree.gso by discriminate; exact Hi|].
          unfold X. rewrite <- (ptr_index_long 488 160 kz) by flia. rewrite <- ci_sizeof_SIN. reflexivity.
        + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss
                              |apply eval_Etempvar; unfold leB, leA; rewrite !PTree.gso by discriminate; exact Hi|].
          rewrite <- (ptr_index_long ori 64 kz) by (change Ptrofs.max_unsigned with 18446744073709551615 in *; flia).
          rewrite <- mt_sizeof_RIN_Z. reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leD) (m1 := m2).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leC) (m1 := m1).
      - apply exec_Sset. eapply ev_tx_field with (delta := 432) (chunk := Mint64);
          [unfold leB, leA; rewrite !PTree.gso by discriminate; exact Htx|exact envu_tx_totalInputValue|reflexivity|flia|exact HT1].
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leD) (m1 := m1).
        + apply exec_Sset. eapply ev_ld with (chunk := Mint64) (base := X + 104);
            [reflexivity|exact envu_sigOutput_value|reflexivity| |flia|flia|flia|].
          * eapply ev_sub; [reflexivity|exact envu_sigInput_txo| |flia|flia|flia].
            apply EvD; unfold leC, leB, leA; rewrite !PTree.gso by discriminate; assumption.
          * rewrite Z.add_0_r. exact R5.
        + eapply exec_Sassign with (v2 := Vlong (Int64.add (in_tot data k) (d_val d)))
            (v := Vlong (Int64.add (in_tot data k) (d_val d))).
          * eapply eval_envu_field_lvalue; [reflexivity|exact envu_tx_totalInputValue|].
            apply eval_envu_deref_struct. unfold leD, leC, leB, leA. rewrite !PTree.gso by discriminate. exact Htx.
          * eapply eval_Ebinop; [apply eval_Etempvar; unfold leD; rewrite PTree.gso by discriminate; apply PTree.gss
                                |apply eval_Etempvar; apply PTree.gss|reflexivity].
          * reflexivity.
          * eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by flia. exact SS. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leE) (m1 := m3).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leE) (m1 := m2).
      - apply exec_Sset. eapply ev_ld with (chunk := Mint64) (base := X);
          [reflexivity|exact envu_sigInput_sequence|reflexivity| |flia|flia|flia|].
        + apply EvD; unfold leD, leC, leB, leA; rewrite !PTree.gso by discriminate; assumption.
        + rewrite HL2 by (right; right; flia). exact R7.
      - exact HExec3. }
    exact HExec4.
  - cbv delta [mt_in_s2] beta iota.
    apply exec_Sset. eapply eval_Ebinop; [apply eval_Etempvar; rewrite GF' by discriminate; exact Hi|apply eval_Econst_int|].
    change (Some (Vlong (Int64.add (Int64.repr kz) (Int64.repr 1))) = Some (Vlong (Int64.repr (Z.of_nat (S k))))).
    rewrite i64_add_repr by flia. replace (Z.of_nat (S k)) with (kz + 1) by (unfold kz; flia). reflexivity.
Qed.

Theorem in_loop dd : forall k le m, (k + dd = Nn)%nat -> in_inv k le m ->
  exists le' m', in_inv Nn le' m' /\
    Clight2.exec_stmt sha_ge e le m (Sloop mt_in_s1 mt_in_s2) E0 le' m' Out_normal.
Proof.
  induction dd as [|dd IH]; intros k le m Hkd HI.
  - replace k with Nn in HI by lia. destruct (in_exit le m HI) as (le' & HI' & HE).
    exists le', m. split; assumption.
  - destruct (in_step k le m ltac:(lia) HI) as (le1 & m1 & le2 & m2 & HI2 & H1 & H2).
    destruct (IH (S k) le2 m2 ltac:(lia) HI2) as (le' & m' & HI' & HE).
    exists le', m'. split; [exact HI'|].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact H1|constructor|exact H2|exact HE].
Qed.
End InLoop.
