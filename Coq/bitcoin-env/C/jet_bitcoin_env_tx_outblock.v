(** [simplicity_bitcoin_mallocTransaction], the output block, complete:
    three context initialisations, the output loop, the two finalisations
    and [outputsHash].  Continuation style: an execution of the rest of the
    body ([mt_rest5]) from the state reached here is an execution of
    [mt_rest4].  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma envu_tx_outputValuesHash : envu_field_at _bitcoinTransaction _outputValuesHash 16.
Proof. exact (mt_hash_offsets 0 _outputValuesHash eq_refl). Qed.
Lemma envu_tx_outputScriptsHash : envu_field_at _bitcoinTransaction _outputScriptsHash 48.
Proof. exact (mt_hash_offsets 1 _outputScriptsHash eq_refl). Qed.

Local Opaque sha_ge.

Section OutBlock.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bRV bCV bRS bCS bRO bCO braw bro : block) (oraw oro ni no : Z).
Variables (val : nat -> int64) (bsp : nat -> block) (osp : nat -> ptrofs) (spb : nat -> list int).
Variable oldb : block -> Prop.

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let OB := 488 + 160 * ni.
Let Nn := Z.to_nat no.
Let items := mk_items out_specs [(bRV, bCV); (bRS, bCS); (bRO, bCO)].

Hypothesis HeI : e!_sha256_init = None.
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU : e!_sha256_u64be = None.
Hypothesis HeF : e!_sha256_finalize = None.
Hypothesis HeCp : e!_copyOutput = None.
Hypothesis Hni : 0 <= ni <= 4294967295.
Hypothesis Hno : 0 <= no <= 4294967295.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis Horo : 0 <= oro /\ oro + 24 * no <= Ptrofs.max_unsigned.
Hypothesis HWf : items_wf e bA items [].
Hypothesis HSepB : ctxs_sep bA (out_cs bCO bCS bCV val spb 0 false false).

(** The states written to the three output hash fields. *)
Definition out_regsV : list int :=
  snd (absorb_i (fst (out_stV val Nn)) (snd (out_stV val Nn)) (sha_pad (Int64.repr (8 * Z.of_nat Nn)))).
Definition out_regsS : list int :=
  snd (absorb_i (fst (out_stS spb Nn)) (snd (out_stS spb Nn)) (sha_pad (Int64.repr (32 * Z.of_nat Nn)))).
Definition out_regsO : list int :=
  let s1 := absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV)) in
  let s2 := absorb_i (fst s1) (snd s1) (be_bytes (norm8 out_regsS)) in
  snd (absorb_i (fst s2) (snd s2) (sha_pad (Int64.add (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32)))).

Theorem mt_outblock_exec le m :
  le!_tx = Some (Vptr bA Ptrofs.zero) -> le!_output = Some (Vptr bA (Ptrofs.repr OB)) ->
  le!_rawTx = Some rawv ->
  (forall it, In it items -> item_perms bA m it) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  (forall b, oldb b -> Mem.valid_block m b /\ b <> bA /\
     b <> bRV /\ b <> bCV /\ b <> bRS /\ b <> bCS /\ b <> bRO /\ b <> bCO) ->
  oldb braw -> (0 < no -> oldb bro) -> (forall j, (j < Nn)%nat -> oldb (bsp j)) ->
  (0 < no -> Mem.load Mptr m braw (oraw + 16) = Some (Vptr bro (Ptrofs.repr oro))) ->
  (forall j, (j < Nn)%nat -> Mem.load Mint64 m bro (oro + 24 * Z.of_nat j) = Some (Vlong (val j))) ->
  (forall j, (j < Nn)%nat -> raw_buffer_at m bro (oro + 24 * Z.of_nat j + 8) (bsp j) (osp j) (spb j)) ->
  Mem.range_perm m bA 0 (OB + 40 * no) Cur Writable ->
  Mem.load Mint64 m bA 456 = Some (Vlong (Int64.repr no)) ->
  Mem.load Mint64 m bA 440 = Some (Vlong Int64.zero) ->
  exists m' le',
    le'!_tx = Some (Vptr bA Ptrofs.zero) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (16 + 4 * Z.of_nat j) = Some (Vint (nth j out_regsV Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (48 + 4 * Z.of_nat j) = Some (Vint (nth j out_regsS Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (80 + 4 * Z.of_nat j) = Some (Vint (nth j out_regsO Int.zero))) /\
    Mem.load Mint64 m' bA 440 = Some (Vlong (out_tot val Nn)) /\
    (forall j, (j < Nn)%nat ->
       Mem.load Mint64 m' bA (OB + 40 * Z.of_nat j) = Some (Vlong (val j)) /\
       forall i, (i < 8)%nat ->
         Mem.load Mint32 m' bA (OB + 40 * Z.of_nat j + 8 + 4 * Z.of_nat i) =
           Some (Vint (nth i (hash_buffer_regs (spb j)) Int.zero))) /\
    (forall ch b ofs, oldb b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall ch ofs, ofs + size_chunk ch <= OB ->
       (ofs + size_chunk ch <= 16 \/ (112 <= ofs /\ ofs + size_chunk ch <= 440) \/ 448 <= ofs) ->
       Mem.load ch m' bA ofs = Mem.load ch m bA ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    (forall t le'' mf out,
       Clight2.exec_stmt sha_ge e le' m' mt_rest5 t le'' mf out ->
       Clight2.exec_stmt sha_ge e le m mt_rest4 t le'' mf out).
Proof.
  intros Htx Hout Hraw HPerm Hdisp HMax Hold HoRaw HoRo HoSp HRo HVals HBufs PA HNo HTot.
  pose proof HWf as HWf0. unfold items in HWf0. cbn [mk_items out_specs combine map items_wf] in HWf0.
  destruct HWf0 as (OkV & _ & OkS & _ & OkO & _).
  destruct OkV as (HeRV & HeCV & _ & _ & _ & NACV & NARV & _).
  destruct OkS as (HeRS & HeCS & _ & _ & _ & NACS & NARS & _).
  destruct OkO as (HeRO & HeCO & _ & _ & _ & NACO & NARO & _).
  destruct HSepB as (NGA & NMA & _).
  assert (VA : Mem.valid_block m bA) by (eapply load_valid_block; exact HNo).
  (* the three initialisations *)
  destruct (inits_exec e bA HeI NGA NMA items [] le m HWf Htx HPerm Hdisp HMax ltac:(constructor))
    as (m1 & HCs1 & HL1 & HP1 & HV1 & HK1).
  unfold items in HCs1. cbn [mk_items out_specs combine map rev app item_entry] in HCs1.
  assert (Hold1 : forall b, oldb b -> Mem.valid_block m1 b /\ b <> bA /\ b <> bCO /\ b <> bCS /\ b <> bCV).
  { intros b Hb. destruct (Hold b Hb) as (Vb & N1 & N2 & N3 & N4 & N5 & N6 & N7).
    split; [apply HV1, Vb|]. repeat split; assumption. }
  assert (Ko1 : forall ch b ofs, oldb b -> Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Hold b Hb) as (Vb & N1 & N2 & N3 & N4 & N5 & N6 & N7).
    apply HL1; [exact Vb|]. intros it Hit. unfold items in Hit. cbn [mk_items out_specs combine map In] in Hit.
    destruct Hit as [<-|[<-|[<-|[]]]]; cbn [item_untouched]; repeat split; auto. }
  assert (Ka1 : forall ch ofs, (ofs + size_chunk ch <= 16 \/ 112 <= ofs) ->
    Mem.load ch m1 bA ofs = Mem.load ch m bA ofs).
  { intros ch ofs Hr. apply HL1; [exact VA|]. intros it Hit. unfold items in Hit.
    cbn [mk_items out_specs combine map In] in Hit.
    destruct Hit as [<-|[<-|[<-|[]]]]; cbn [item_untouched];
      (split; [assumption|split; [assumption|right; clear - Hr; lia]]). }
  set (le0 := PTree.set _i__1 (Vlong (Int64.repr 0)) le).
  assert (HI0 : out_inv bA bCO bCS bCV braw oraw ni val spb oldb m1 0 le0 m1).
  { unfold out_inv, le0. split; [apply PTree.gss|]. rewrite !PTree.gso by discriminate.
    split; [exact Htx|]. split; [exact Hout|]. split; [exact Hraw|].
    split; [exists false, false; apply ctxs_live_all; exact HCs1|].
    split; [rewrite Ka1 by (right; clear; lia); exact HTot|].
    split; [intros j Hj; clear - Hj; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; auto. }
  (* the loop *)
  destruct (out_loop Hmodel e bA bCO bCS bCV braw bro oraw oro ni no val bsp osp spb oldb m1
    HeCS HeCV HeH HeU HeCp Hni Hno Horaw Horo HSepB Hold1 HoRaw HoRo HoSp) with (d := Nn) (k := 0%nat) (le := le0) (m := m1)
    as (le2 & m2 & HI2 & HLoop).
  { intros Hp. rewrite Ko1 by exact HoRaw. exact (HRo Hp). }
  { intros j Hj. rewrite Ko1 by (apply HoRo; unfold Nn in Hj; clear - Hj; lia). apply HVals, Hj. }
  { intros j Hj. destruct (HBufs j Hj) as (len & B1 & B2 & B3 & B4 & B5 & B6). exists len.
    rewrite !Ko1 by (apply HoRo; unfold Nn in Hj; clear - Hj; lia). repeat (split; [assumption|]). split; [apply HV1, B5|].
    intros i Hi. rewrite Ko1 by (apply HoSp; exact Hj). apply B6, Hi. }
  { intros o Ho. apply HP1, PA, Ho. }
  { apply HV1, VA. }
  { rewrite Ka1 by (right; clear; lia). exact HNo. }
  { reflexivity. }
  { exact HI0. }
  destruct HI2 as (Hi2 & Htx2 & Hout2 & Hraw2 & (oS & oV & HC2) & HT2 & HO2 & HFo2 & HFa2 & HPm2 & HV2).
  set (cs := out_cs bCO bCS bCV val spb Nn oS oV) in *.
  assert (HSepC : ctxs_sep bA cs).
  { eapply ctxs_sep_shape; [|exact HSepB]. reflexivity. }
  assert (VA2 : Mem.valid_block m2 bA) by (apply HV2, HV1, VA).
  (* finalize values, scripts *)
  destruct (live_finalize Hmodel bA cs (fun _ => True) 2%nat bCV 16 _ _ _ _ HSepC eq_refl Logic.I m2 HC2)
    as (m3 & vr3 & HCall3 & HReg3 & HC3 & HL3 & HP3 & HV3).
  fold out_regsV in HReg3.
  pose (lv1 := fun j : nat => (fun _ : nat => True) j /\ j <> 2%nat).
  assert (HC3' : ctxs_live m3 bA cs lv1) by exact HC3.
  assert (L11 : lv1 1%nat) by (split; [exact Logic.I|discriminate]).
  assert (L10 : lv1 0%nat) by (split; [exact Logic.I|discriminate]).
  destruct (live_finalize Hmodel bA cs lv1 1%nat bCS 48 _ _ _ _ HSepC eq_refl L11 m3 HC3')
    as (m4 & vr4 & HCall4 & HReg4 & HC4 & HL4 & HP4 & HV4).
  pose (lv2 := fun j : nat => lv1 j /\ j <> 1%nat).
  assert (HC4' : ctxs_live m4 bA cs lv2) by exact HC4.
  assert (L20 : lv2 0%nat) by (split; [exact L10|discriminate]).
  fold out_regsS in HReg4.
  assert (VA3 : Mem.valid_block m3 bA) by (apply HV3, VA2).
  assert (VA4 : Mem.valid_block m4 bA) by (apply HV4, VA3).
  (* outputsHash *)
  set (oV16 := Ptrofs.repr 16). set (oS48 := Ptrofs.repr 48).
  destruct (live_hash Hmodel bA cs lv2 0%nat bCO 80 _ _ _ _ HSepC eq_refl L20 m4 bA oV16 (norm8 out_regsV) HC4' eq_refl)
    as (m5 & HCall5 & HC5 & HL5 & HP5 & HV5).
  { change (Ptrofs.unsigned oV16) with 16. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned oV16) with 16. rewrite norm8_nth by exact Hj.
    rewrite HL4; [apply HReg3, Hj|exact VA3|exact NACS|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia]. }
  set (cs5 := upd cs 0 (bCO, 80, fst (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV))),
    snd (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV))),
    Int64.add Int64.zero (Int64.repr 32), uc_overflow false Int64.zero (Int64.repr 32))) in *.
  assert (HSep5 : ctxs_sep bA cs5) by (eapply ctxs_sep_shape; [|exact HSepB]; reflexivity).
  destruct (live_hash Hmodel bA cs5 lv2 0%nat bCO 80 _ _ _ _ HSep5 eq_refl L20 m5 bA oS48 (norm8 out_regsS) HC5 eq_refl)
    as (m6 & HCall6 & HC6 & HL6 & HP6 & HV6).
  { change (Ptrofs.unsigned oS48) with 48. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned oS48) with 48. rewrite norm8_nth by exact Hj.
    rewrite HL5; [apply HReg4, Hj|exact VA4|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia]. }
  set (cs6 := upd cs5 0 (bCO, 80,
    fst (absorb_i (fst (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV))))
           (snd (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV)))) (be_bytes (norm8 out_regsS))),
    snd (absorb_i (fst (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV))))
           (snd (absorb_i [] sha256_iv_words (be_bytes (norm8 out_regsV)))) (be_bytes (norm8 out_regsS))),
    Int64.add (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32),
    uc_overflow (uc_overflow false Int64.zero (Int64.repr 32)) (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 32))) in *.
  assert (HSep6 : ctxs_sep bA cs6) by (eapply ctxs_sep_shape; [|exact HSepB]; reflexivity).
  destruct (live_finalize Hmodel bA cs6 lv2 0%nat bCO 80 _ _ _ _ HSep6 eq_refl L20 m6 HC6)
    as (m7 & vr7 & HCall7 & HReg7 & _ & HL7 & HP7 & HV7).
  fold out_regsO in HReg7.
  assert (VA5 : Mem.valid_block m5 bA) by (apply HV5, VA4).
  assert (VA6 : Mem.valid_block m6 bA) by (apply HV6, VA5).
  (* loads of bA through the five steps *)
  assert (KA : forall ch ofs, (ofs + size_chunk ch <= 16 \/ 112 <= ofs) ->
    Mem.load ch m7 bA ofs = Mem.load ch m2 bA ofs).
  { intros ch ofs Hr.
    rewrite HL7; [|exact VA6|exact NACO|right; clear - Hr; lia].
    rewrite HL6; [|exact VA5|exact NACO|right; clear - Hr; lia].
    rewrite HL5; [|exact VA4|exact NACO|right; clear - Hr; lia].
    rewrite HL4; [|exact VA3|exact NACS|right; clear - Hr; lia].
    apply HL3; [exact VA2|exact NACV|right; clear - Hr; lia]. }
  exists m7, le2.
  split; [exact Htx2|].
  split.
  { intros j Hj.
    rewrite HL7; [|exact VA6|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    rewrite HL6; [|exact VA5|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    rewrite HL5; [|exact VA4|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    rewrite HL4; [|exact VA3|exact NACS|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    apply HReg3, Hj. }
  split.
  { intros j Hj.
    rewrite HL7; [|exact VA6|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    rewrite HL6; [|exact VA5|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    rewrite HL5; [|exact VA4|exact NACO|right; left; change (size_chunk Mint32) with 4; clear - Hj; lia].
    apply HReg4, Hj. }
  split; [intros j Hj; apply HReg7, Hj|].
  split; [rewrite KA by (right; clear; lia); exact HT2|].
  split.
  { intros j Hj. destruct (HO2 j Hj) as [HOv HOs]. split.
    - rewrite KA; [exact HOv|right; unfold OB; clear - Hni; lia].
    - intros i Hi. rewrite KA; [apply HOs, Hi|right; unfold OB; clear - Hni; lia]. }
  split.
  { intros ch b ofs Hb. destruct (Hold1 b Hb) as (Vb1 & NbA & NbO & NbS & NbV).
    assert (Vb2 : Mem.valid_block m2 b) by (apply HV2, Vb1).
    rewrite HL7; [|apply HV6, HV5, HV4, HV3, Vb2|exact NbO|left; exact NbA].
    rewrite HL6; [|apply HV5, HV4, HV3, Vb2|exact NbO|left; exact NbA].
    rewrite HL5; [|apply HV4, HV3, Vb2|exact NbO|left; exact NbA].
    rewrite HL4; [|apply HV3, Vb2|exact NbS|left; exact NbA].
    rewrite HL3; [|exact Vb2|exact NbV|left; exact NbA].
    rewrite HFo2 by exact Hb. apply Ko1, Hb. }
  split.
  { intros ch ofs HB Hz.
    rewrite KA by (clear - Hz; lia). rewrite HFa2 by assumption. apply Ka1. clear - Hz; lia. }
  split.
  { intros b ofs k p Hp.
    assert (Hp2 : Mem.perm m2 b ofs k p) by (apply HPm2, HP1, Hp).
    assert (Hp3 : Mem.perm m3 b ofs k p) by (apply HP3; [eapply Mem.perm_valid_block; exact Hp2|exact Hp2]).
    assert (Hp4 : Mem.perm m4 b ofs k p) by (apply HP4; [eapply Mem.perm_valid_block; exact Hp3|exact Hp3]).
    assert (Hp5 : Mem.perm m5 b ofs k p) by (apply HP5; [eapply Mem.perm_valid_block; exact Hp4|exact Hp4]).
    assert (Hp6 : Mem.perm m6 b ofs k p) by (apply HP6; [eapply Mem.perm_valid_block; exact Hp5|exact Hp5]).
    apply HP7; [eapply Mem.perm_valid_block; exact Hp6|exact Hp6]. }
  split; [intros b Hb; apply HV7, HV6, HV5, HV4, HV3, HV2, HV1, Hb|].
  intros t le'' mf out HRest.
  change mt_rest4 with (Ssequence mt_outblock mt_rest5).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := le2) (m1 := m7); [|exact HRest].
  rewrite (mt_outblock_shape [(bRV, bCV); (bRS, bCS); (bRO, bCO)] eq_refl).
  apply HK1. rewrite mt_out_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m1).
    - apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
    - exact HLoop. }
  cbv delta [mt_out_fin] beta iota.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
  { eapply mt_call_finalize; [exact HeF|exact HeCV|exact HCall3]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
  { eapply mt_call_finalize; [exact HeF|exact HeCS|exact HCall4]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m5).
  { eapply mt_call_hash with (bx := bCO) (bt := bA) (ot := oV16);
      [exact HeH|exact HeCO|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_outputValuesHash]|reflexivity|exact HCall5]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m6).
  { eapply mt_call_hash with (bx := bCO) (bt := bA) (ot := oS48);
      [exact HeH|exact HeCO|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_outputScriptsHash]|reflexivity|exact HCall6]. }
  eapply mt_call_finalize; [exact HeF|exact HeCO|exact HCall7].
Qed.
End OutBlock.
