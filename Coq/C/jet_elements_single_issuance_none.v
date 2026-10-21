(** The actual no-issuance payload branch and its finalization. Four absent
    asset/amount markers, the two proof digests, and an absent blinding marker
    cross a SHA block boundary. No inactive issuance payload is read. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_readBit_layout.
Require Import C.jet_read8s_layout.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_buffer_input.
Require Import C.jet_bitcoin_tx_hash C.jet_bitcoin_composite_hash.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_prim C.jet_elements_conf_hash_bridge C.jet_elements_field_eval.
Require Import C.jet_elements_env_tx_calls C.jet_elements_single_input_optional.
Require Import C.jet_elements_single_issuance_spec C.jet_elements_single_issuance_prep.
Require Import C.jet_elements_input_utxo_payload C.jet_elements_outpoints_hash_program.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_be32_write.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation ISS := (Tstruct _assetIssuance noattr).

Definition eis_hash_stmt (field : ident) : statement :=
  Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP;
     Eaddrof (Efield (Ederef (Etempvar _issuance (tptr ISS)) ISS) field MID) (tptr MID)].

Lemma eis_none_shape :
  eis_none = Ssequence (eih_uchar_stmt Int.zero)
    (Ssequence (eih_uchar_stmt Int.zero)
      (Ssequence (eih_uchar_stmt Int.zero)
        (Ssequence (eih_uchar_stmt Int.zero)
          (Ssequence (eis_hash_stmt _assetRangeProofHash)
            (Ssequence (eis_hash_stmt _tokenRangeProofHash) (eih_uchar_stmt Int.zero)))))).
Proof. reflexivity. Qed.

Lemma eis_hash_stmt_exec field delta e le m mf bx bin ofs :
  elements_field_at _assetIssuance field delta ->
  0 <= delta -> delta + 32 <= 280 ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  e!_sha256_hash = None -> e!_ctx = Some (bx, CTX) ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_hash)
    [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + delta))] E0 mf Vundef ->
  Clight2.exec_stmt sha_ge e le m (eis_hash_stmt field) E0 le mf Out_normal.
Proof.
  intros HF HD HM HO HMax HG HC HI HCall.
  eapply mt_call_hash; [exact HG|exact HC| |reflexivity|exact HCall].
  eapply eval_Eaddrof. rewrite <- (elements_ptr_add_repr ofs delta) by lia.
  eapply eval_elements_field_lvalue; [reflexivity|exact HF|].
  apply eval_elements_deref_struct. exact HI.
Qed.

Lemma eis_asset_proof_offset : elements_field_at _assetIssuance _assetRangeProofHash 104.
Proof. vm_compute; reflexivity. Qed.
Lemma eis_token_proof_offset : elements_field_at _assetIssuance _tokenRangeProofHash 136.
Proof. vm_compute; reflexivity. Qed.

Definition eis_none_bytes (ha ht : hash256) : list int :=
  ((([Int.zero; Int.zero; Int.zero; Int.zero] ++ be_bytes (hash256_reg ha)) ++
    be_bytes (hash256_reg ht)) ++ [Int.zero]).

Lemma eis_none_bytes_canonical ha ht :
  eis_none_bytes ha ht = map word8_array_value
    (elements_single_issuance_bytes (inl tt) (inl tt) (from_hash256 ha) (from_hash256 ht) (inl tt)).
Proof.
  unfold eis_none_bytes, elements_single_issuance_bytes.
  rewrite !map_app, <- !elements_hash_words_bytes. reflexivity.
Qed.

Lemma eis_none_message_length ha ht :
  length (elements_single_issuance_bytes (inl tt) (inl tt)
    (from_hash256 ha) (from_hash256 ht) (inl tt)) = 69%nat.
Proof.
  pose proof (f_equal (@length int) (eis_none_bytes_canonical ha ht)) as HL.
  rewrite map_length in HL. rewrite <- HL. unfold eis_none_bytes.
  rewrite !app_length, !be_bytes_length, !hash256_len. reflexivity.
Qed.

Section NoIssuance.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_none_finalize e le m bin ofs ha ht :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  e!_sha256_hash = None -> e!_sha256_uchar = None -> e!_ctx = Some (bx, CTX) ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  uint32_array_at m bin (ofs + 104) (hash256_reg ha) ->
  uint32_array_at m bin (ofs + 136) (hash256_reg ht) ->
  exists mp mf vr,
    Clight2.exec_stmt sha_ge e le m eis_none E0 le mp Out_normal /\
    Clight2.eval_funcall sha_ge mp (Internal f_sha256_finalize)
      [Vptr bx Ptrofs.zero] E0 mf vr /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg (sha256_bytes_of
        (elements_single_issuance_bytes (inl tt) (inl tt)
          (from_hash256 ha) (from_hash256 ht) (inl tt)))) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros X0 HO HM Hix Him HG HU HC HI HA HT.
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m _ _ Int.zero _ _ X0 eq_refl)
    as (m1 & C1 & X1 & L1 & P1 & V1).
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m1 _ _ Int.zero _ _ X1 eq_refl)
    as (m2 & C2 & X2 & L2 & P2 & V2).
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m2 _ _ Int.zero _ _ X2 eq_refl)
    as (m3 & C3 & X3 & L3 & P3 & V3).
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m3 _ _ Int.zero _ _ X3 eq_refl)
    as (m4 & C4 & X4 & L4 & P4 & V4).
  assert (VB : Mem.valid_block m bin).
  { assert (HL : Mem.load Mint32 m bin (ofs + 104 + 4 * Z.of_nat 0) =
      Some (Vint (nth 0 (hash256_reg ha) Int.zero))).
    { apply HA, nth_error_nth'. rewrite hash256_len. lia. }
    eapply load_valid_block; exact HL. }
  assert (HA4 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m4 bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 104)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg ha) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite L4 by (auto using V1, V2, V3). rewrite L3 by (auto using V1, V2).
    rewrite L2 by auto. rewrite L1 by assumption.
    apply HA, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m4 bin (Ptrofs.repr (ofs + 104))
    _ _ (hash256_reg ha) _ _ X4 (hash256_len ha)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HA4)
    as (m5 & C5 & X5 & L5 & P5 & V5).
  assert (HT5 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m5 bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 136)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg ht) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite L5 by (auto using V1, V2, V3, V4).
    rewrite L4 by (auto using V1, V2, V3). rewrite L3 by (auto using V1, V2).
    rewrite L2 by auto. rewrite L1 by assumption.
    apply HT, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m5 bin (Ptrofs.repr (ofs + 136))
    _ _ (hash256_reg ht) _ _ X5 (hash256_len ht)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HT5)
    as (m6 & C6 & X6 & L6 & P6 & V6).
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m6 _ _ Int.zero _ _ X6 eq_refl)
    as (m7 & C7 & X7 & L7 & P7 & V7).
  rewrite <- !absorb_i_app in X7.
  destruct (ctxi_finalize bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m7 _ _ _ _ X7)
    as (mf & CF & RF & LF & PF & VF).
  match type of CF with Clight2.eval_funcall _ _ _ _ _ _ ?v => exists m7, mf, v end.
  split.
  { rewrite eis_none_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
    { eapply eih_uchar_stmt_exec; [exact HU|exact HC|reflexivity|exact C1]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
    { eapply eih_uchar_stmt_exec; [exact HU|exact HC|reflexivity|exact C2]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m3).
    { eapply eih_uchar_stmt_exec; [exact HU|exact HC|reflexivity|exact C3]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
    { eapply eih_uchar_stmt_exec; [exact HU|exact HC|reflexivity|exact C4]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m5).
    { eapply eis_hash_stmt_exec; [exact eis_asset_proof_offset|lia|lia|exact HO|exact HM|
        exact HG|exact HC|exact HI|exact C5]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m6).
    { eapply eis_hash_stmt_exec; [exact eis_token_proof_offset|lia|lia|exact HO|exact HM|
        exact HG|exact HC|exact HI|exact C6]. }
    eapply eih_uchar_stmt_exec; [exact HU|exact HC|reflexivity|exact C7]. }
  split; [exact CF|].
  split.
  { rewrite eiu_stream_regs.
    rewrite <- eis_none_bytes_canonical. unfold eis_none_bytes.
    rewrite eis_none_message_length. rewrite <- !app_assoc. exact RF. }
  assert (VV : forall b, Mem.valid_block m b -> Mem.valid_block m7 b).
  { intros b V. apply V7, V6, V5, V4, V3, V2, V1, V. }
  split.
  { intros ch b o V Nx Nm. rewrite LF by auto.
    rewrite L7 by (auto 8 using V1, V2, V3, V4, V5, V6).
    rewrite L6 by (auto 8 using V1, V2, V3, V4, V5).
    rewrite L5 by (auto using V1, V2, V3, V4).
    rewrite L4 by (auto using V1, V2, V3). rewrite L3 by (auto using V1, V2).
    rewrite L2 by auto. apply L1; assumption. }
  split.
  { intros b o k p V P. apply PF; [auto|].
    apply P7; [auto 8 using V1, V2, V3, V4, V5, V6|].
    apply P6; [auto 8 using V1, V2, V3, V4, V5|].
    apply P5; [auto using V1, V2, V3, V4|].
    apply P4; [auto using V1, V2, V3|]. apply P3; [auto using V1, V2|].
    apply P2; [auto|]. apply P1; assumption. }
  intros b V. apply VF, VV, V.
Qed.
End NoIssuance.
