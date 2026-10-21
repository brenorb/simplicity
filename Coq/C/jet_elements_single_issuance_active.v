(** Complete active issuance payload branches and finalization. Literal
    construction, amount selection and both blinding branches execute here;
    neither intermediate execution nor the resulting digest is a premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_read8s_layout C.jet_buffer_input C.jet_bitcoin_composite_hash.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_issuance_amount_hash_spec.
Require Import C.jet_elements_blinding_entropy_hash_spec C.jet_elements_conf_hash_bridge.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_single_issuance_asset C.jet_elements_single_issuance_amount.
Require Import C.jet_elements_single_issuance_blinding C.jet_elements_single_issuance_tail.
Require Import C.jet_elements_input_utxo_payload.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_elements_support_sha_ctxi.
Require Import C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_uchars_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation AMT := (Tstruct _confAmount noattr).

Lemma eis_some_shape : eis_some =
  Ssequence eis_asset_prefix (Ssequence eis_asset_amount_stmt
    (Ssequence eis_token_prefix (Ssequence eis_token_amount_stmt eis_active_tail))).
Proof. reflexivity. Qed.

Definition eis_some_message (isnew : bool) (asset token : hash256) (aa ta : amountWith unit)
    (hpa hpt q ent : hash256) : list (Ty.tySem Word8) :=
  elements_single_issuance_bytes (inr (from_hash256 asset, encode_amount aa))
    (inr (from_hash256 token, encode_amount (eis_selected_amount isnew ta)))
    (from_hash256 hpa) (from_hash256 hpt) (inr (eis_blinding_pair isnew q ent)).

Lemma eis_some_message_bytes isnew asset token aa ta hpa hpt q ent :
  (((map word8_array_value (elements_asset_bytes (encode_asset (Explicit asset : assetWith unit))) ++
    map word8_array_value (elements_amount_bytes (encode_amount aa))) ++
    map word8_array_value (elements_asset_bytes (encode_asset (Explicit token : assetWith unit)))) ++
    map word8_array_value (elements_amount_bytes (encode_amount (eis_selected_amount isnew ta)))) ++
    eis_tail_bytes isnew hpa hpt q ent =
  map word8_array_value (eis_some_message isnew asset token aa ta hpa hpt q ent).
Proof.
  unfold eis_some_message, elements_single_issuance_bytes, issuance_asset_amount_bytes,
    elements_asset_amount_bytes, blinding_entropy_bytes, eis_tail_bytes.
  cbn [fst snd]. rewrite !map_app, <- !elements_hash_words_bytes.
  change (word8_array_value jet_bitcoin_ctx_hash_spec.byte_one) with Int.one.
  cbn [map]. rewrite <- eis_blinding_bytes_canonical, <- !app_assoc. reflexivity.
Qed.

Section Active.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_some_finalize (isnew : bool) e le m bin ofs ba bt bz bb
    asset token aa ta hpa hpt q ent :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  NoDup [ba; bt; bz; bb] ->
  (forall b, In b [ba; bt; bz; bb] -> b <> bin /\ b <> bx /\ b <> bm /\ b <> GC /\ b <> GM) ->
  e!_ctx = Some (bx, CTX) -> e!___compound = Some (ba, CONF) ->
  e!___compound__1 = Some (bt, CONF) -> e!___compound__2 = Some (bz, AMT) ->
  e!___compound__3 = Some (bb, tarray tuchar 32) ->
  e!_simplicity_sha256_confAsset = None -> e!_simplicity_sha256_confAmt = None ->
  e!_sha256_hash = None -> e!_sha256_uchar = None -> e!_sha256_uchars = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind isnew)) ->
  uint32_array_at m bin (ofs + 168) (hash256_reg asset) ->
  uint32_array_at m bin (ofs + 200) (hash256_reg token) ->
  amount_rep m bin (ofs + 232) aa ->
  (isnew = true -> amount_rep m bin (ofs + 32) ta) ->
  uint32_array_at m bin (ofs + 104) (hash256_reg hpa) ->
  uint32_array_at m bin (ofs + 136) (hash256_reg hpt) ->
  uint32_array_at m bin ofs (hash256_reg q) ->
  (isnew = false -> uint32_array_at m bin (ofs + 72) (hash256_reg ent)) ->
  Mem.range_perm m ba 0 36 Cur Writable -> Mem.range_perm m bt 0 36 Cur Writable ->
  Mem.range_perm m bz 0 40 Cur Writable -> Mem.range_perm m bb 0 32 Cur Writable ->
  exists mp mf vr,
    Clight2.exec_stmt sha_ge e le m eis_some E0
      (PTree.set _t'5 (Vint (eis_kind isnew)) (eis_token_le le isnew bin ofs bz)) mp Out_normal /\
    Clight2.eval_funcall sha_ge mp (Internal f_sha256_finalize) [Vptr bx Ptrofs.zero] E0 mf vr /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg (sha256_bytes_of
        (eis_some_message isnew asset token aa ta hpa hpt q ent))) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> ba -> b <> bt -> b <> bz -> b <> bb ->
      b <> bx -> b <> bm -> Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HN HF HC HBa HBt HBz HBb HGA HGM HH HU HUS HI HO HM Hix Him HT
    HAsset HToken HAA HTA HPA HPT HQ HE PA PT PZ PB.
  pose proof (HF ba ltac:(cbn; auto)) as (Hai & Hax & Ham & Hag & Hac).
  pose proof (HF bt ltac:(cbn; auto)) as (Hti & Htx & Htm & Htg & Htc).
  pose proof (HF bz ltac:(cbn; auto)) as (Hzi & Hzx & Hzm & Hzg & Hzc).
  pose proof (HF bb ltac:(cbn; auto)) as (Hbi & Hbx & Hbm & Hbg & Hbc).
  assert (ND : ba <> bt /\ ba <> bz /\ ba <> bb /\ bt <> bz /\ bt <> bb /\ bz <> bb).
  { clear -HN. repeat rewrite NoDup_cons_iff in HN. cbn [In] in HN. intuition congruence. }
  destruct ND as (Hat & Haz & Hab & Htz & Htb & Hzb).
  assert (VB : Mem.valid_block m bin) by (eapply load_valid_block; exact HT).
  assert (VT : Mem.valid_block m bt).
  { eapply Mem.perm_valid_block. apply (PT 0). lia. }
  assert (VZ : Mem.valid_block m bz).
  { eapply Mem.perm_valid_block. apply (PZ 0). lia. }
  assert (VBb : Mem.valid_block m bb).
  { eapply Mem.perm_valid_block. apply (PB 0). lia. }
  set (A := map word8_array_value (elements_asset_bytes (encode_asset (Explicit asset : assetWith unit)))).
  set (V := map word8_array_value (elements_amount_bytes (encode_amount aa))).
  set (T := map word8_array_value (elements_asset_bytes (encode_asset (Explicit token : assetWith unit)))).
  set (W := map word8_array_value (elements_amount_bytes (encode_amount (eis_selected_amount isnew ta)))).
  destruct (exec_eis_id_hash Hmodel bx bm false e le m ba bin ofs asset [] sha256_iv_words Int64.zero false
    Hmx Hgx Hgm Hcx Hcm HX HBa HC HGA HI Hai Hax Ham Hag Hac HO HM HAsset PA)
    as (m1 & C1 & X1 & L1 & P1 & V1).
  fold A in X1. change (Int64.add Int64.zero (Int64.repr 33)) with (Int64.repr 33) in X1.
  assert (AA1 : amount_rep m1 bin (ofs + 232) aa).
  { eapply amount_rep_mono; [exact HAA|]. intros ch o v _ _ HL.
    rewrite L1 by (auto using not_eq_sym). exact HL. }
  destruct (exec_eis_asset_amount Hmodel bx bm Hmx Hgx Hgm Hcx Hcm
    e le m1 bin ofs aa _ _ _ _ X1 HC HGM HI HO HM Hix Him AA1)
    as (m2 & C2 & X2 & L2 & P2 & V2).
  fold A V in X2.
  assert (LB2 : forall ch o, Mem.load ch m2 bin o = Mem.load ch m bin o).
  { intros ch o. rewrite L2 by auto. apply L1; auto using not_eq_sym. }
  assert (TW2 : uint32_array_at m2 bin (ofs + 200) (hash256_reg token)).
  { intros j v HJ. rewrite LB2. apply HToken, HJ. }
  assert (PT2 : Mem.range_perm m2 bt 0 36 Cur Writable).
  { intros o P. apply P2; [auto|]. apply P1; [exact VT|apply PT, P]. }
  destruct (exec_eis_id_hash Hmodel bx bm true e le m2 bt bin ofs token _ _ _ _
    Hmx Hgx Hgm Hcx Hcm X2 HBt HC HGA HI Hti Htx Htm Htg Htc HO HM TW2 PT2)
    as (m3 & C3 & X3 & L3 & P3 & V3).
  fold A V T in X3.
  assert (LB3 : forall ch o, Mem.load ch m3 bin o = Mem.load ch m bin o).
  { intros ch o. rewrite L3 by (auto using not_eq_sym). apply LB2. }
  assert (TA3 : isnew = true -> amount_rep m3 bin (ofs + 32) ta).
  { intro E. eapply amount_rep_mono; [apply HTA, E|].
    intros ch o v _ _ HL. rewrite LB3. exact HL. }
  assert (PZ3 : Mem.range_perm m3 bz 0 40 Cur Writable).
  { intros o P. apply P3; [auto|]. apply P2; [auto|]. apply P1; [exact VZ|apply PZ, P]. }
  destruct (exec_eis_token_amount Hmodel bx bm Hmx Hgx Hgm Hcx Hcm isnew e le m3 bin ofs bz ta
    _ _ _ _ X3 HC HGM HBz HI HO HM Hix Him Hzx Hzm Hzg Hzc
    ltac:(rewrite LB3; exact HT) TA3 PZ3)
    as (m4 & C4 & X4 & L4 & P4 & V4).
  fold A V T W in X4.
  assert (LB4 : forall ch o, Mem.load ch m4 bin o = Mem.load ch m bin o).
  { intros ch o. rewrite L4 by (auto using not_eq_sym). apply LB3. }
  assert (PB4 : Mem.range_perm m4 bb 0 32 Cur Writable).
  { intros o P. apply P4; [auto|]. apply P3; [auto|]. apply P2; [auto|].
    apply P1; [exact VBb|apply PB, P]. }
  assert (HI4 : (eis_token_le le isnew bin ofs bz)!_issuance = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold eis_token_le. rewrite !PTree.gso by discriminate. exact HI. }
  destruct (exec_eis_active_tail Hmodel bx bm Hmx Hgx Hgm Hcx Hcm isnew e
    (eis_token_le le isnew bin ofs bz) m4 bin ofs bb hpa hpt q ent _ _ _ _ X4
    HC HBb HUS HH HU HI4 HO HM Hix Him Hbi Hbx Hbm Hbg Hbc
    ltac:(rewrite LB4; exact HT)
    ltac:(intros j v HJ; rewrite LB4; apply HPA, HJ)
    ltac:(intros j v HJ; rewrite LB4; apply HPT, HJ)
    ltac:(intros j v HJ; rewrite LB4; apply HQ, HJ)
    ltac:(intros E j v HJ; rewrite LB4; apply (HE E), HJ) PB4)
    as (mp & vp & CP & XP & LP & PP & VP).
  rewrite <- !absorb_i_app in XP.
  destruct (ctxi_finalize bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mp _ _ _ _ XP)
    as (mf & CF & RF & LF & PF & VF).
  pose proof (eis_some_message_bytes isnew asset token aa ta hpa hpt q ent) as HB.
  fold A V T W in HB.
  assert (HL : length (eis_some_message isnew asset token aa ta hpa hpt q ent) =
    (33 + length V + 33 + length W + 129)%nat).
  { pose proof (f_equal (@length int) HB) as HEq.
    rewrite map_length, !app_length, eis_tail_bytes_length in HEq.
    assert (LA : length A = 33%nat) by apply eiu_asset_len.
    assert (LT : length T = 33%nat) by apply eiu_asset_len.
    rewrite LA, LT in HEq. symmetry. exact HEq. }
  assert (HCnt : Int64.add
    (Int64.add (Int64.add (Int64.add (Int64.repr 33) (Int64.repr (Z.of_nat (length V))))
      (Int64.repr 33)) (Int64.repr (Z.of_nat (length W)))) (Int64.repr 129) =
    Int64.repr (Z.of_nat (length (eis_some_message isnew asset token aa ta hpa hpt q ent)))).
  { rewrite HL. destruct (eiu_amount_len aa) as [HV|HV];
      destruct (eiu_amount_len (eis_selected_amount isnew ta)) as [HW|HW];
      fold V in HV; fold W in HW; rewrite HV, HW; reflexivity. }
  rewrite HCnt in RF. rewrite <- !app_assoc in HB. rewrite HB in RF.
  match type of CF with Clight2.eval_funcall _ _ _ _ _ _ ?v => exists mp, mf, v end.
  split.
  { rewrite eis_some_shape. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1); [exact C1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2); [exact C2|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m3); [exact C3|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
      (le1 := eis_token_le le isnew bin ofs bz) (m1 := m4); [exact C4|exact CP]. }
  split; [exact CF|]. split.
  { rewrite eiu_stream_regs. exact RF. }
  assert (VP0 : forall b, Mem.valid_block m b -> Mem.valid_block mp b).
  { intros b V0. apply VP, V4, V3, V2, V1, V0. }
  split.
  { intros ch b o V0 Na Nt Nz Nb Nx Nm. rewrite LF by auto.
    rewrite LP by (auto 8 using V1, V2, V3, V4).
    rewrite L4 by (auto using V1, V2, V3). rewrite L3 by (auto using V1, V2).
    rewrite L2 by auto. apply L1; assumption. }
  split.
  { intros b o k p V0 P. apply PF; [auto|].
    apply PP; [auto 8 using V1, V2, V3, V4|]. apply P4; [auto using V1, V2, V3|].
    apply P3; [auto using V1, V2|]. apply P2; [auto|]. apply P1; assumption. }
  intros b V0. apply VF, VP0, V0.
Qed.
End Active.
