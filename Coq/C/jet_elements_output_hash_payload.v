(** Actual SHA calls for the output_hash payload: asset, amount, optional
    nonce, script digest, range-proof digest, then finalize. Reuses the
    confidential helpers and the general streaming bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_read8s_layout.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha_ctx8_model.
Require Import C.jet_buffer_input.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_nonce_hash_spec C.jet_elements_output_hash_spec.
Require Import C.jet_elements_conf_hash_repr C.jet_elements_conf_hash_bridge C.jet_elements_nonce_hash_repr.
Require Import C.jet_elements_input_utxo_payload.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_uchars_exec.
Require Import C.jet_elements_support_sha_be32_write C.jet_elements_support_sha_finalize_exec.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_input_hash_spec.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition eoh_hash_of (a : assetWith unit) (v : amountWith unit) (n : option nonce)
    (s r : hash256) : hash256 :=
  sha256_bytes_of (elements_output_hash_bytes (encode_asset a, encode_amount v)
    (encode_nonce n) (from_hash256 s) (from_hash256 r)).

Lemma eoh_nonce_len n :
  length (map word8_array_value (elements_nonce_bytes (encode_nonce n))) = 1%nat \/
  length (map word8_array_value (elements_nonce_bytes (encode_nonce n))) = 33%nat.
Proof.
  rewrite !map_length. destruct n as [[[odd h]|h]|]; [right|right|left];
    cbn [encode_nonce nonce_conf encode_asset conf_toBit elements_nonce_bytes length];
    try rewrite vector_values_length; reflexivity.
Qed.

Section Payload.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eval_eoh_payload m bin ofs a v n s r :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  0 <= ofs -> ofs + 248 <= Ptrofs.max_unsigned ->
  bin <> bx -> bin <> bm ->
  asset_rep m bin ofs a ->
  amount_rep m bin (ofs + 104) v ->
  nonce_rep m bin (ofs + 144) n ->
  uint32_array_at m bin (ofs + 180) (hash256_reg s) ->
  uint32_array_at m bin (ofs + 68) (hash256_reg r) ->
  exists ma mv mn ms mr mf vr,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr ofs)] E0 ma Vundef /\
    Clight2.eval_funcall sha_ge ma (Internal f_simplicity_sha256_confAmt)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 104))] E0 mv Vundef /\
    Clight2.eval_funcall sha_ge mv (Internal f_simplicity_sha256_confNonce)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 144))] E0 mn Vundef /\
    Clight2.eval_funcall sha_ge mn (Internal f_sha256_hash)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 180))] E0 ms Vundef /\
    Clight2.eval_funcall sha_ge ms (Internal f_sha256_hash)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 68))] E0 mr Vundef /\
    Clight2.eval_funcall sha_ge mr (Internal f_sha256_finalize)
      [Vptr bx Ptrofs.zero] E0 mf vr /\
    (forall j, (j < 8)%nat ->
      Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg (eoh_hash_of a v n s r)) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k q, Mem.valid_block m b -> Mem.perm m b o k q -> Mem.perm mf b o k q) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC Ho HM Hbinx Hbinm HA HV HN HS HR.
  assert (Vbin : Mem.valid_block m bin).
  { destruct HA as [_ HP]. eapply load_valid_block; exact HP. }
  set (A := map word8_array_value (elements_asset_bytes (encode_asset a))).
  set (B := map word8_array_value (elements_amount_bytes (encode_amount v))).
  set (N := map word8_array_value (elements_nonce_bytes (encode_nonce n))).
  destruct (eval_sha256_asset_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm m [] sha256_iv_words
    Int64.zero false bin ofs a HC ltac:(lia) Hbinx Hbinm HA)
    as (ma & CA & AX & LA & PA & VA).
  fold A in AX.
  assert (HAlen : length A = 33%nat) by apply eiu_asset_len.
  rewrite HAlen in AX.
  change (Int64.add Int64.zero (Int64.repr (Z.of_nat 33))) with (Int64.repr 33) in AX.
  assert (HV' : amount_rep ma bin (ofs + 104) v).
  { eapply amount_rep_mono; [exact HV|]. intros ch o w _ _ HL.
    rewrite LA; [exact HL|exact Vbin|exact Hbinx|exact Hbinm]. }
  destruct (eval_sha256_amount_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm ma _ _
    (Int64.repr 33) _ bin (ofs + 104) v AX ltac:(lia) Hbinx Hbinm HV')
    as (mv & CV & VX & LV & PV & VV).
  fold A B in VX.
  rewrite <- !absorb_i_app in VX.
  assert (HN' : nonce_rep mv bin (ofs + 144) n).
  { destruct HN as [HD HP]. split.
    - intros HSome j x Hj. rewrite LV by auto. rewrite LA by auto. apply HD; assumption.
    - rewrite LV by auto. rewrite LA by auto. exact HP. }
  destruct (eval_sha256_nonce_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm mv _ _ _ _
    bin (ofs + 144) n VX ltac:(lia) Hbinx Hbinm HN') as (mn & CN & NX & LN & PN & VN).
  fold A B N in NX. rewrite <- !absorb_i_app in NX.
  assert (HS' : forall j, (j < 8)%nat ->
    Mem.load Mint32 mn bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 180)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg s) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite LN by auto. rewrite LV by auto. rewrite LA by auto.
    apply HS, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mn bin (Ptrofs.repr (ofs + 180))
    _ _ (hash256_reg s) _ _ NX (hash256_len s)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HS') as (ms & CS & SX & LS & PS & VS).
  rewrite <- !absorb_i_app in SX.
  assert (HR' : forall j, (j < 8)%nat ->
    Mem.load Mint32 ms bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 68)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg r) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite LS by auto. rewrite LN by auto. rewrite LV by auto. rewrite LA by auto.
    apply HR, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel ms bin (Ptrofs.repr (ofs + 68))
    _ _ (hash256_reg r) _ _ SX (hash256_len r)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HR') as (mr & CR & RX & LR & PR & VR).
  rewrite <- !absorb_i_app in RX.
  destruct (ctxi_finalize bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mr _ _ _ _ RX)
    as (mf & CF & RF & LF & PF & VF).
  assert (HB : length B = 9%nat \/ length B = 33%nat) by apply eiu_amount_len.
  assert (HNlen : length N = 1%nat \/ length N = 33%nat) by apply eoh_nonce_len.
  assert (HStream : (((A ++ B) ++ N) ++ be_bytes (hash256_reg s)) ++ be_bytes (hash256_reg r) =
    map word8_array_value (elements_output_hash_bytes (encode_asset a, encode_amount v)
      (encode_nonce n) (from_hash256 s) (from_hash256 r))).
  { unfold A, B, N, elements_output_hash_bytes, elements_asset_amount_bytes.
    rewrite !map_app, !elements_hash_words_bytes. reflexivity. }
  match type of CF with Clight2.eval_funcall _ _ _ _ _ _ ?rv =>
    exists ma, mv, mn, ms, mr, mf, rv end.
  split; [exact CA|]. split; [exact CV|]. split; [exact CN|]. split; [exact CS|].
  split; [exact CR|]. split; [exact CF|].
  split.
  { unfold eoh_hash_of. rewrite eiu_stream_regs.
    rewrite HStream in RF.
    assert (HCnt : Int64.add (Int64.add
      (Int64.add (Int64.add (Int64.repr 33) (Int64.repr (Z.of_nat (length B))))
        (Int64.repr (Z.of_nat (length N)))) (Int64.repr 32)) (Int64.repr 32) =
      Int64.repr (Z.of_nat (length (elements_output_hash_bytes (encode_asset a, encode_amount v)
        (encode_nonce n) (from_hash256 s) (from_hash256 r))))).
    { unfold elements_output_hash_bytes, elements_asset_amount_bytes.
      rewrite !app_length, elements_asset_bytes_length, !vector_values_length.
      destruct HB as [HB|HB]; destruct HNlen as [HNlen|HNlen];
        rewrite HB, HNlen;
        unfold B, N in HB, HNlen; rewrite !map_length in HB, HNlen;
        cbn [fst snd]; rewrite HB, HNlen; reflexivity. }
    rewrite HCnt in RF. exact RF. }
  split.
  { intros ch b o V Nx Nm.
    pose proof (VA _ V) as Vma. pose proof (VV _ Vma) as Vmv.
    pose proof (VN _ Vmv) as Vmn. pose proof (VS _ Vmn) as Vms.
    pose proof (VR _ Vms) as Vmr.
    rewrite LF by assumption. rewrite LR by assumption. rewrite LS by assumption.
    rewrite LN by assumption. rewrite LV by assumption. apply LA; assumption. }
  split.
  { intros b o k q V P.
    pose proof (VA _ V) as Vma. pose proof (VV _ Vma) as Vmv.
    pose proof (VN _ Vmv) as Vmn. pose proof (VS _ Vmn) as Vms.
    pose proof (VR _ Vms) as Vmr.
    apply PF; [exact Vmr|]. apply PR; [exact Vms|]. apply PS; [exact Vmn|].
    apply PN; [exact Vmv|]. apply PV; [exact Vma|]. apply PA; assumption. }
  { intros b V. apply VF, VR, VS, VN, VV, VA; exact V. }
Qed.
End Payload.
