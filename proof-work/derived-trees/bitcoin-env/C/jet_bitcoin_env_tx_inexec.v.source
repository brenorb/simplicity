(** [simplicity_bitcoin_mallocTransaction], the input block: the eight
    initialisations, the loop, the six finalisations and the two derived
    hashes (inputUTXOsHash, inputsHash).  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_ctxo.
Require Import C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls C.jet_bitcoin_env_ctxs_core.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txid C.jet_bitcoin_env_tx_inblock C.jet_bitcoin_env_tx_txhash.
Require Import C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inops C.jet_bitcoin_env_tx_inloop.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma envu_tx_inputOutpointsHash : envu_field_at _bitcoinTransaction _inputOutpointsHash 112.
Proof. exact (mt_hash_offsets 3 _inputOutpointsHash eq_refl). Qed.
Lemma envu_tx_inputValuesHash : envu_field_at _bitcoinTransaction _inputValuesHash 144.
Proof. exact (mt_hash_offsets 4 _inputValuesHash eq_refl). Qed.
Lemma envu_tx_inputScriptsHash : envu_field_at _bitcoinTransaction _inputScriptsHash 176.
Proof. exact (mt_hash_offsets 5 _inputScriptsHash eq_refl). Qed.
Lemma envu_tx_inputSequencesHash : envu_field_at _bitcoinTransaction _inputSequencesHash 240.
Proof. exact (mt_hash_offsets 7 _inputSequencesHash eq_refl). Qed.
Lemma envu_tx_inputAnnexesHash : envu_field_at _bitcoinTransaction _inputAnnexesHash 272.
Proof. exact (mt_hash_offsets 8 _inputAnnexesHash eq_refl). Qed.

Local Opaque sha_ge.

(** Separation of the contexts that [inits_exec] creates follows from the
    well-formedness of the items. *)
Lemma ctxs_sep_cons bA (c0 : ctx_entry) cs :
  ctxs_sep bA cs -> ctx_block c0 <> bA -> GC <> ctx_block c0 -> GM <> ctx_block c0 ->
  0 <= ctx_out c0 -> ctx_out c0 + 32 <= Ptrofs.max_unsigned ->
  (forall c, In c cs ->
     ctx_block c <> ctx_block c0 /\ (ctx_out c + 32 <= ctx_out c0 \/ ctx_out c0 + 32 <= ctx_out c)) ->
  ctxs_sep bA (c0 :: cs).
Proof.
  intros (NG & NM & H1 & H2) A1 A2 A3 A4 A5 HS. split; [exact NG|]. split; [exact NM|]. split.
  - intros [|k] c Hk; cbn in Hk; [injection Hk as <-; repeat split; assumption|exact (H1 k c Hk)].
  - intros [|i] [|j] ci cj Hi Hj Hij; cbn in Hi, Hj.
    + congruence.
    + injection Hi as <-. destruct (HS cj (nth_error_In _ _ Hj)) as [D1 D2]. split; [exact (not_eq_sym D1)|lia].
    + injection Hj as <-. destruct (HS ci (nth_error_In _ _ Hi)) as [D1 D2]. split; [exact D1|lia].
    + apply (H2 i j ci cj Hi Hj). congruence.
Qed.

Lemma items_wf_sep e bA (its : list init_item) : forall cs,
  items_wf e bA its cs -> ctxs_sep bA cs -> ctxs_sep bA (rev (map item_entry its) ++ cs).
Proof.
  induction its as [|it its IH]; intros cs HW HS; [exact HS|].
  cbn [map rev]. rewrite <- app_assoc. cbn [app].
  destruct it as [[[[[r c] f] d] bR] bC]. destruct HW as (Ok & Sp & HW').
  apply IH; [exact HW'|]. cbn [item_ok] in Ok.
  destruct Ok as (_ & _ & _ & (D0 & D1) & _ & NAC & _ & _ & NGC & NMC & _).
  apply ctxs_sep_cons; cbn [item_entry ctx_block ctx_out];
    [exact HS|exact (not_eq_sym NAC)|exact NGC|exact NMC|exact D0
    |change Ptrofs.max_unsigned with 18446744073709551615; lia|].
  intros c0 Hc0. specialize (Sp c0 Hc0). cbn [item_sep] in Sp. destruct Sp as (_ & S2 & _ & S4).
  split; [exact S2|exact S4].
Qed.

Lemma ctxs_sep_nil bA : GC <> bA -> GM <> bA -> ctxs_sep bA [].
Proof.
  intros NG NM. split; [exact NG|]. split; [exact NM|]. split.
  - intros [|k] c Hk; discriminate.
  - intros [|i] j ci cj Hi; discriminate.
Qed.

(** State words written to another field survive an operation. *)
Lemma regs_keep bA bx ob m m' o (rs : list int) :
  mfrP (opP bA bx ob) m m' -> Mem.valid_block m bA -> bA <> bx -> (o + 32 <= ob \/ ob + 32 <= o) ->
  (forall i, (i < 8)%nat -> Mem.load Mint32 m bA (o + 4 * Z.of_nat i) = Some (Vint (nth i rs Int.zero))) ->
  (forall i, (i < 8)%nat -> Mem.load Mint32 m' bA (o + 4 * Z.of_nat i) = Some (Vint (nth i rs Int.zero))).
Proof.
  intros (L & _ & _) VA N Hr H i Hi. rewrite L; [apply H, Hi|exact VA|].
  split; [exact N|right]. change (size_chunk Mint32) with 4. lia.
Qed.

Ltac zrange := first [left; vm_compute; discriminate | right; vm_compute; discriminate].
Ltac carry mprev HF VA N :=
  repeat match goal with
  | H : forall i : nat, (i < 8)%nat ->
          Mem.load Mint32 mprev _ (?o + 4 * Z.of_nat i) = Some (Vint (nth i ?rs Int.zero)) |- _ =>
      let H' := fresh in
      pose proof (regs_keep _ _ _ _ _ o rs HF VA N ltac:(zrange) H) as H'; clear H; rename H' into H
  end.

(** The states written to the eight input hash fields. *)
Definition fin_regs (st : list int * list int) (c : int64) : list int :=
  snd (absorb_i (fst st) (snd st) (sha_pad c)).
Definition c32 (c : int64) : int64 := Int64.add c (Int64.repr 32).

Section Regs.
Variables (data : nat -> in_data) (n : nat).
Definition in_regsP : list int := fin_regs (in_stOP data n) (in_cntOP n).
Definition in_regsV : list int := fin_regs (in_stV data n) (in_cnt 8 n).
Definition in_regsS : list int := fin_regs (in_stSc data n) (in_cnt 32 n).
Definition in_regsQ : list int := fin_regs (in_stSeq data n) (in_cnt 4 n).
Definition in_regsN : list int := fin_regs (in_stAn data n) (in_nAn data n).
Definition in_regsG : list int := fin_regs (in_stSS data n) (in_cnt 32 n).
Definition in_regsU : list int :=
  fin_regs (ab (ab st0 (be_bytes (norm8 in_regsV))) (be_bytes (norm8 in_regsS))) (c32 (c32 Int64.zero)).
Definition in_regsI : list int :=
  fin_regs (ab (ab (ab st0 (be_bytes (norm8 in_regsP))) (be_bytes (norm8 in_regsQ))) (be_bytes (norm8 in_regsN)))
    (c32 (c32 (c32 Int64.zero))).
End Regs.

Section InBlock.
Variable Hmodel : memcpy_model.
Variables (e : env) (bA bRP bP bRV bV bRS bS bRU bU bRQ bQ bRN bN bRG bG bRI bI braw bri : block).
Variables (oraw ori ni : Z) (data : nat -> in_data) (oldb : block -> Prop).

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let Nn := Z.to_nat ni.
Let pairs := [(bRP, bP); (bRV, bV); (bRS, bS); (bRU, bU); (bRQ, bQ); (bRN, bN); (bRG, bG); (bRI, bI)].
Let items := mk_items in_specs pairs.
Let blocks := [bI; bG; bN; bQ; bU; bS; bV; bP].
Let allb := [bRP; bP; bRV; bV; bRS; bS; bRU; bU; bRQ; bQ; bRN; bN; bRG; bG; bRI; bI].
Local Notation allL := (fun _ : nat => True).

Hypothesis HeI : e!_sha256_init = None.
Hypothesis HeH : e!_sha256_hash = None.
Hypothesis HeU4 : e!_sha256_u32be = None.
Hypothesis HeU8 : e!_sha256_u64be = None.
Hypothesis HeUc : e!_sha256_uchar = None.
Hypothesis HeF : e!_sha256_finalize = None.
Hypothesis HeCp : e!_copyInput = None.
Hypothesis Hni : 0 <= ni <= 4294967295.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.
Hypothesis Hori : 0 <= ori /\ ori + 64 * ni <= Ptrofs.max_unsigned.
Hypothesis NGA : GC <> bA.
Hypothesis NMA : GM <> bA.
Hypothesis HWf : items_wf e bA items [].

Theorem mt_inblock_exec le m :
  mt_le1 le rawv bA ni ->
  (forall it, In it items -> item_perms bA m it) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  (forall b, oldb b -> Mem.valid_block m b /\ b <> bA /\ ~ In b allb) ->
  oldb braw -> (0 < ni -> oldb bri) ->
  (0 < ni -> Mem.load Mptr m braw (oraw + 8) = Some (Vptr bri (Ptrofs.repr ori))) ->
  (forall j, (j < Nn)%nat -> raw_in_at oldb m bri (ori + 64 * Z.of_nat j) (data j)) ->
  Mem.range_perm m bA 0 (488 + 160 * ni) Cur Writable ->
  Mem.load Mint64 m bA 448 = Some (Vlong (Int64.repr ni)) ->
  Mem.load Mint64 m bA 432 = Some (Vlong Int64.zero) ->
  Mem.load Mint8unsigned m bA 480 = Some (Vint Int.one) ->
  exists m' le',
    mt_le1 le' rawv bA ni /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (112 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsP data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (144 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsV data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (176 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsS data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (208 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsU data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (240 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsQ data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (272 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsN data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (304 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsG data Nn) Int.zero))) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bA (336 + 4 * Z.of_nat j) = Some (Vint (nth j (in_regsI data Nn) Int.zero))) /\
    Mem.load Mint64 m' bA 432 = Some (Vlong (in_tot data Nn)) /\
    Mem.load Mint8unsigned m' bA 480 = Some (Vint (in_final data Nn)) /\
    (forall j, (j < Nn)%nat -> in_rec m' bA (488 + 160 * Z.of_nat j) (data j)) /\
    (forall ch b ofs, oldb b -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall ch ofs,
       (ofs + size_chunk ch <= 112 \/ (368 <= ofs /\ ofs + size_chunk ch <= 432) \/
        (440 <= ofs /\ ofs + size_chunk ch <= 480)) ->
       Mem.load ch m' bA ofs = Mem.load ch m bA ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    (forall t le'' mf out,
       Clight2.exec_stmt sha_ge e le' m' mt_rest4 t le'' mf out ->
       Clight2.exec_stmt sha_ge e le m mt_rest3 t le'' mf out).
Proof.
  intros (Hraw & Htx & Hin & Hout) HPerm Hdisp HMax Hold HoRaw HoRi HRi HRaw PA HNi HTot HFin.
  pose proof HWf as HWf0. unfold items, pairs in HWf0. cbn [mk_items in_specs combine map items_wf] in HWf0.
  destruct HWf0 as (OkP & _ & OkV & _ & OkS & _ & OkU & _ & OkQ & _ & OkN & _ & OkG & _ & OkI & _).
  destruct OkP as (_ & HeCP & _ & _ & _ & NAP & NRP & _).
  destruct OkV as (_ & HeCV & _ & _ & _ & NAV & NRV & _).
  destruct OkS as (_ & HeCS & _ & _ & _ & NAS & NRS & _).
  destruct OkU as (_ & HeCU & _ & _ & _ & NAU & NRU & _).
  destruct OkQ as (_ & HeCQ & _ & _ & _ & NAQ & NRQ & _).
  destruct OkN as (_ & HeCN & _ & _ & _ & NAN & NRN & _).
  destruct OkG as (_ & HeCG & _ & _ & _ & NAG & NRG & _).
  destruct OkI as (_ & HeCI & _ & _ & _ & NAI & NRI & _).
  assert (VA : Mem.valid_block m bA) by (eapply load_valid_block; exact HNi).
  assert (HNA : ~ In bA blocks).
  { unfold blocks. cbn [In]. intros HIn. repeat (destruct HIn as [E|HIn]; [symmetry in E; contradiction|]). exact HIn. }
  assert (Hsub : forall x, In x blocks -> In x allb).
  { intros x Hx. unfold blocks, allb in *. cbn [In] in *. tauto. }
  pose proof (items_wf_sep e bA items [] HWf (ctxs_sep_nil bA NGA NMA)) as HSep.
  rewrite app_nil_r in HSep.
  (* the eight initialisations *)
  destruct (inits_exec e bA HeI NGA NMA items [] le m HWf Htx HPerm Hdisp HMax ltac:(constructor))
    as (m1 & HCs1 & HL1 & HP1 & HV1 & HK1).
  rewrite app_nil_r in HCs1.
  pose proof (LS_intro m1 bA _ allL HSep (ctxs_live_all _ _ _ HCs1)) as HLS1.
  unfold items, pairs in HLS1. cbn [mk_items in_specs combine map rev app item_entry core_of] in HLS1.
  assert (Ko1 : forall ch b ofs, oldb b -> Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Hold b Hb) as (Vb & NbA & Nbb).
    assert (NB : forall x, In x allb -> b <> x) by (intros x Hx ->; exact (Nbb Hx)).
    apply HL1; [exact Vb|]. intros it Hit. unfold items, pairs in Hit. cbn [mk_items in_specs combine map In] in Hit.
    repeat (destruct Hit as [<-|Hit];
      [cbn [item_untouched]; split; [apply NB; unfold allb; inb|split; [apply NB; unfold allb; inb|left; exact NbA]]|]).
    contradiction. }
  assert (Ka1 : forall ch ofs, (ofs + size_chunk ch <= 112 \/ 368 <= ofs) ->
    Mem.load ch m1 bA ofs = Mem.load ch m bA ofs).
  { intros ch ofs Hr. apply HL1; [exact VA|]. intros it Hit. unfold items, pairs in Hit.
    cbn [mk_items in_specs combine map In] in Hit.
    repeat (destruct Hit as [<-|Hit];
      [cbn [item_untouched]; split; [assumption|split; [assumption|right; clear - Hr; lia]]|]).
    contradiction. }
  assert (Hold1 : forall b, oldb b -> Mem.valid_block m1 b /\ b <> bA /\ ~ In b blocks).
  { intros b Hb. destruct (Hold b Hb) as (Vb & NbA & Nbb).
    split; [apply HV1, Vb|]. split; [exact NbA|]. intros Hx. exact (Nbb (Hsub b Hx)). }
  set (le0 := PTree.set _i (Vlong (Int64.repr 0)) le).
  assert (HI0 : in_inv bA bI bG bN bQ bU bS bV bP braw oraw ni data oldb m1 0 le0 m1).
  { unfold in_inv, le0. split; [apply PTree.gss|]. rewrite !PTree.gso by discriminate.
    split; [exact Htx|]. split; [exact Hin|]. split; [exact Hraw|]. split; [exact Hout|].
    split; [exact HLS1|].
    split; [rewrite Ka1 by (right; clear; lia); exact HTot|].
    split; [rewrite Ka1 by (right; clear; lia); exact HFin|].
    split; [intros j Hj; clear - Hj; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; auto. }
  (* the loop *)
  destruct (in_loop Hmodel e bA bI bG bN bQ bU bS bV bP braw bri oraw ori ni data oldb m1
    HeCP HeCV HeCS HeCQ HeCN HeCG HeH HeU4 HeU8 HeUc HeCp Hni Horaw Hori HNA Hold1 HoRaw HoRi)
    with (dd := Nn) (k := 0%nat) (le := le0) (m := m1) as (le2 & m2 & HI2 & HLoop).
  { intros Hp. rewrite Ko1 by exact HoRaw. exact (HRi Hp). }
  { intros j Hj. eapply raw_in_frame; [exact (HRaw j Hj)|apply HoRi; unfold Nn in Hj; clear - Hj; lia|exact Ko1|exact HV1]. }
  { intros o Ho. apply HP1, PA, Ho. }
  { rewrite Ka1 by (right; clear; lia). exact HNi. }
  { reflexivity. }
  { exact HI0. }
  destruct HI2 as (Hi2 & Htx2 & Hin2 & Hraw2 & Hout2 & HLS2 & HT2 & HFi2 & HR2 & HFo2 & HFa2 & HPm2 & HV2).
  fold Nn in HLS2, HT2, HFi2, HR2.
  unfold in_cores, mk_core in HLS2.
  assert (VA2 : Mem.valid_block m2 bA) by (apply HV2, HV1, VA).
  set (Q := rngP bA blocks 112 368).
  assert (Opq : forall bx ob mi mj, In bx blocks -> 112 <= ob -> ob + 32 <= 368 ->
    mfrP Q m2 mi -> mfrP (opP bA bx ob) mi mj -> mfrP Q m2 mj).
  { intros bx ob mi mj H1 H2 H3 H4 H5. eapply mfrP_trans; [exact H4|]. eapply opP_rng; eassumption. }
  pose proof (mfrP_refl Q m2) as G2.
  (* finalize outpoints, values, scripts, sequences, annexes, scriptSigs *)
  pose (lv1 := fun j : nat => allL j /\ j <> 7%nat).
  pose (lv2 := fun j : nat => lv1 j /\ j <> 6%nat).
  pose (lv3 := fun j : nat => lv2 j /\ j <> 5%nat).
  pose (lv4 := fun j : nat => lv3 j /\ j <> 3%nat).
  pose (lv5 := fun j : nat => lv4 j /\ j <> 2%nat).
  pose (lv6 := fun j : nat => lv5 j /\ j <> 1%nat).
  pose (lv7 := fun j : nat => lv6 j /\ j <> 4%nat).
  assert (L16 : lv1 6%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L25 : lv2 5%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L33 : lv3 3%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L42 : lv4 2%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L51 : lv5 1%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L64 : lv6 4%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  assert (L70 : lv7 0%nat) by (repeat (split; [|discriminate]); exact Logic.I).
  let cc := ls_cores HLS2 in
  destruct (LS_finalize Hmodel bA cc allL 7%nat bP 112 _ _ _ eq_refl Logic.I m2 HLS2)
    as (m3 & vr3 & HCall3 & HRegP & HLS3 & HF3).
  let cc := ls_cores HLS3 in change (LS m3 bA cc lv1) in HLS3.
  assert (G3 : mfrP Q m2 m3) by (eapply (Opq bP 112 m2 m3); [unfold blocks; inb|lia|lia|exact G2|exact HF3]).
  assert (VA3 : Mem.valid_block m3 bA) by (apply (proj2 (proj2 HF3)), VA2).
  let cc := ls_cores HLS3 in
  destruct (LS_finalize Hmodel bA cc lv1 6%nat bV 144 _ _ _ eq_refl L16 m3 HLS3)
    as (m4 & vr4 & HCall4 & HRegV & HLS4 & HF4).
  let cc := ls_cores HLS4 in change (LS m4 bA cc lv2) in HLS4.
  carry m3 HF4 VA3 NAV.
  assert (G4 : mfrP Q m2 m4) by (eapply (Opq bV 144 m3 m4); [unfold blocks; inb|lia|lia|exact G3|exact HF4]).
  assert (VA4 : Mem.valid_block m4 bA) by (apply (proj2 (proj2 HF4)), VA3).
  let cc := ls_cores HLS4 in
  destruct (LS_finalize Hmodel bA cc lv2 5%nat bS 176 _ _ _ eq_refl L25 m4 HLS4)
    as (m5 & vr5 & HCall5 & HRegS & HLS5 & HF5).
  let cc := ls_cores HLS5 in change (LS m5 bA cc lv3) in HLS5.
  carry m4 HF5 VA4 NAS.
  assert (G5 : mfrP Q m2 m5) by (eapply (Opq bS 176 m4 m5); [unfold blocks; inb|lia|lia|exact G4|exact HF5]).
  assert (VA5 : Mem.valid_block m5 bA) by (apply (proj2 (proj2 HF5)), VA4).
  let cc := ls_cores HLS5 in
  destruct (LS_finalize Hmodel bA cc lv3 3%nat bQ 240 _ _ _ eq_refl L33 m5 HLS5)
    as (m6 & vr6 & HCall6 & HRegQ & HLS6 & HF6).
  let cc := ls_cores HLS6 in change (LS m6 bA cc lv4) in HLS6.
  carry m5 HF6 VA5 NAQ.
  assert (G6 : mfrP Q m2 m6) by (eapply (Opq bQ 240 m5 m6); [unfold blocks; inb|lia|lia|exact G5|exact HF6]).
  assert (VA6 : Mem.valid_block m6 bA) by (apply (proj2 (proj2 HF6)), VA5).
  let cc := ls_cores HLS6 in
  destruct (LS_finalize Hmodel bA cc lv4 2%nat bN 272 _ _ _ eq_refl L42 m6 HLS6)
    as (m7 & vr7 & HCall7 & HRegN & HLS7 & HF7).
  let cc := ls_cores HLS7 in change (LS m7 bA cc lv5) in HLS7.
  carry m6 HF7 VA6 NAN.
  assert (G7 : mfrP Q m2 m7) by (eapply (Opq bN 272 m6 m7); [unfold blocks; inb|lia|lia|exact G6|exact HF7]).
  assert (VA7 : Mem.valid_block m7 bA) by (apply (proj2 (proj2 HF7)), VA6).
  let cc := ls_cores HLS7 in
  destruct (LS_finalize Hmodel bA cc lv5 1%nat bG 304 _ _ _ eq_refl L51 m7 HLS7)
    as (m8 & vr8 & HCall8 & HRegG & HLS8 & HF8).
  let cc := ls_cores HLS8 in change (LS m8 bA cc lv6) in HLS8.
  carry m7 HF8 VA7 NAG.
  assert (G8 : mfrP Q m2 m8) by (eapply (Opq bG 304 m7 m8); [unfold blocks; inb|lia|lia|exact G7|exact HF8]).
  assert (VA8 : Mem.valid_block m8 bA) by (apply (proj2 (proj2 HF8)), VA7).
  (* inputUTXOsHash *)
  set (o144 := Ptrofs.repr 144). set (o176 := Ptrofs.repr 176).
  let cc := ls_cores HLS8 in
  destruct (LS_hash Hmodel bA cc lv6 4%nat bU 208 _ _ _ eq_refl L64 m8 bA o144 (norm8 (in_regsV data Nn)) HLS8 eq_refl)
    as (m9 & HCall9 & HLS9 & HF9).
  { change (Ptrofs.unsigned o144) with 144. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned o144) with 144. rewrite norm8_nth by exact Hj. apply HRegV, Hj. }
  cbn [upd] in HLS9.
  carry m8 HF9 VA8 NAU.
  assert (G9 : mfrP Q m2 m9) by (eapply (Opq bU 208 m8 m9); [unfold blocks; inb|lia|lia|exact G8|exact HF9]).
  assert (VA9 : Mem.valid_block m9 bA) by (apply (proj2 (proj2 HF9)), VA8).
  let cc := ls_cores HLS9 in
  destruct (LS_hash Hmodel bA cc lv6 4%nat bU 208 _ _ _ eq_refl L64 m9 bA o176 (norm8 (in_regsS data Nn)) HLS9 eq_refl)
    as (m10 & HCall10 & HLS10 & HF10).
  { change (Ptrofs.unsigned o176) with 176. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned o176) with 176. rewrite norm8_nth by exact Hj. apply HRegS, Hj. }
  cbn [upd] in HLS10.
  carry m9 HF10 VA9 NAU.
  assert (G10 : mfrP Q m2 m10) by (eapply (Opq bU 208 m9 m10); [unfold blocks; inb|lia|lia|exact G9|exact HF10]).
  assert (VA10 : Mem.valid_block m10 bA) by (apply (proj2 (proj2 HF10)), VA9).
  let cc := ls_cores HLS10 in
  destruct (LS_finalize Hmodel bA cc lv6 4%nat bU 208 _ _ _ eq_refl L64 m10 HLS10)
    as (m11 & vr11 & HCall11 & HRegU & HLS11 & HF11).
  let cc := ls_cores HLS11 in change (LS m11 bA cc lv7) in HLS11.
  carry m10 HF11 VA10 NAU.
  assert (G11 : mfrP Q m2 m11) by (eapply (Opq bU 208 m10 m11); [unfold blocks; inb|lia|lia|exact G10|exact HF11]).
  assert (VA11 : Mem.valid_block m11 bA) by (apply (proj2 (proj2 HF11)), VA10).
  (* inputsHash *)
  set (o112 := Ptrofs.repr 112). set (o240 := Ptrofs.repr 240). set (o272 := Ptrofs.repr 272).
  let cc := ls_cores HLS11 in
  destruct (LS_hash Hmodel bA cc lv7 0%nat bI 336 _ _ _ eq_refl L70 m11 bA o112 (norm8 (in_regsP data Nn)) HLS11 eq_refl)
    as (m12 & HCall12 & HLS12 & HF12).
  { change (Ptrofs.unsigned o112) with 112. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned o112) with 112. rewrite norm8_nth by exact Hj. apply HRegP, Hj. }
  cbn [upd] in HLS12.
  carry m11 HF12 VA11 NAI.
  assert (G12 : mfrP Q m2 m12) by (eapply (Opq bI 336 m11 m12); [unfold blocks; inb|lia|lia|exact G11|exact HF12]).
  assert (VA12 : Mem.valid_block m12 bA) by (apply (proj2 (proj2 HF12)), VA11).
  let cc := ls_cores HLS12 in
  destruct (LS_hash Hmodel bA cc lv7 0%nat bI 336 _ _ _ eq_refl L70 m12 bA o240 (norm8 (in_regsQ data Nn)) HLS12 eq_refl)
    as (m13 & HCall13 & HLS13 & HF13).
  { change (Ptrofs.unsigned o240) with 240. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned o240) with 240. rewrite norm8_nth by exact Hj. apply HRegQ, Hj. }
  cbn [upd] in HLS13.
  carry m12 HF13 VA12 NAI.
  assert (G13 : mfrP Q m2 m13) by (eapply (Opq bI 336 m12 m13); [unfold blocks; inb|lia|lia|exact G12|exact HF13]).
  assert (VA13 : Mem.valid_block m13 bA) by (apply (proj2 (proj2 HF13)), VA12).
  let cc := ls_cores HLS13 in
  destruct (LS_hash Hmodel bA cc lv7 0%nat bI 336 _ _ _ eq_refl L70 m13 bA o272 (norm8 (in_regsN data Nn)) HLS13 eq_refl)
    as (m14 & HCall14 & HLS14 & HF14).
  { change (Ptrofs.unsigned o272) with 272. change Ptrofs.max_unsigned with 18446744073709551615. clear; lia. }
  { intros j Hj. change (Ptrofs.unsigned o272) with 272. rewrite norm8_nth by exact Hj. apply HRegN, Hj. }
  cbn [upd] in HLS14.
  carry m13 HF14 VA13 NAI.
  assert (G14 : mfrP Q m2 m14) by (eapply (Opq bI 336 m13 m14); [unfold blocks; inb|lia|lia|exact G13|exact HF14]).
  assert (VA14 : Mem.valid_block m14 bA) by (apply (proj2 (proj2 HF14)), VA13).
  let cc := ls_cores HLS14 in
  destruct (LS_finalize Hmodel bA cc lv7 0%nat bI 336 _ _ _ eq_refl L70 m14 HLS14)
    as (m15 & vr15 & HCall15 & HRegI & _ & HF15).
  carry m14 HF15 VA14 NAI.
  assert (G15 : mfrP Q m2 m15) by (eapply (Opq bI 336 m14 m15); [unfold blocks; inb|lia|lia|exact G14|exact HF15]).
  destruct G15 as (L15 & P15 & V15).
  assert (LA : forall ch ofs, (ofs + size_chunk ch <= 112 \/ 368 <= ofs) ->
    Mem.load ch m15 bA ofs = Mem.load ch m2 bA ofs).
  { intros ch ofs Hr. apply L15; [exact VA2|]. split; [exact HNA|right; exact Hr]. }
  exists m15, le2.
  split; [repeat split; assumption|].
  split; [exact HRegP|]. split; [exact HRegV|]. split; [exact HRegS|]. split; [exact HRegU|].
  split; [exact HRegQ|]. split; [exact HRegN|]. split; [exact HRegG|]. split; [exact HRegI|].
  split; [rewrite LA by (right; clear; lia); exact HT2|].
  split; [rewrite LA by (right; clear; lia); exact HFi2|].
  split.
  { intros j Hj. eapply in_rec_frame; [exact (HR2 j Hj)|]. intros ch ofs H1 H2. apply LA. right. clear - H1. lia. }
  split.
  { intros ch b ofs Hb. destruct (Hold1 b Hb) as (Vb1 & NbA & Nbb).
    rewrite L15; [|apply HV2, Vb1|split; [exact Nbb|left; exact NbA]].
    rewrite HFo2 by exact Hb. apply Ko1, Hb. }
  split.
  { intros ch ofs Hz. rewrite LA by (clear - Hz; lia). rewrite HFa2 by exact Hz. apply Ka1. clear - Hz; lia. }
  split; [intros b ofs k p Hp; apply P15, HPm2, HP1, Hp|].
  split; [intros b Hb; apply V15, HV2, HV1, Hb|].
  intros t le'' mf out HRest.
  change mt_rest3 with (Ssequence mt_inblock mt_rest4).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := t) (le1 := le2) (m1 := m15); [|exact HRest].
  rewrite (mt_inblock_shape pairs eq_refl).
  apply HK1. rewrite mt_in_tail_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m1).
    - apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
    - exact HLoop. }
  cbv delta [mt_in_fin] beta iota.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
  { eapply mt_call_finalize; [exact HeF|exact HeCP|exact HCall3]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
  { eapply mt_call_finalize; [exact HeF|exact HeCV|exact HCall4]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m5).
  { eapply mt_call_finalize; [exact HeF|exact HeCS|exact HCall5]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m6).
  { eapply mt_call_finalize; [exact HeF|exact HeCQ|exact HCall6]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m7).
  { eapply mt_call_finalize; [exact HeF|exact HeCN|exact HCall7]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m8).
  { eapply mt_call_finalize; [exact HeF|exact HeCG|exact HCall8]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m9).
  { eapply mt_call_hash with (bx := bU) (bt := bA) (ot := o144);
      [exact HeH|exact HeCU|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_inputValuesHash]|reflexivity|exact HCall9]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m10).
  { eapply mt_call_hash with (bx := bU) (bt := bA) (ot := o176);
      [exact HeH|exact HeCU|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_inputScriptsHash]|reflexivity|exact HCall10]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m11).
  { eapply mt_call_finalize; [exact HeF|exact HeCU|exact HCall11]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m12).
  { eapply mt_call_hash with (bx := bI) (bt := bA) (ot := o112);
      [exact HeH|exact HeCI|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_inputOutpointsHash]|reflexivity|exact HCall12]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m13).
  { eapply mt_call_hash with (bx := bI) (bt := bA) (ot := o240);
      [exact HeH|exact HeCI|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_inputSequencesHash]|reflexivity|exact HCall13]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m14).
  { eapply mt_call_hash with (bx := bI) (bt := bA) (ot := o272);
      [exact HeH|exact HeCI|apply ev_tx_mid_addr; [exact Htx2|exact envu_tx_inputAnnexesHash]|reflexivity|exact HCall14]. }
  eapply mt_call_finalize; [exact HeF|exact HeCI|exact HCall15].
Qed.
End InBlock.
