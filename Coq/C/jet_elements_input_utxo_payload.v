(** Four actual SHA calls for an Elements UTXO's asset, amount and script
    digest. The resulting registers are those of the primitive program's
    serialized bytes, including messages crossing a compression boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_read8s_layout.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha_ctx8_model.
Require Import C.jet_buffer_input.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_elements_input_utxo_hash_spec.
Require Import C.jet_elements_conf_hash_repr C.jet_elements_conf_hash_bridge.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_uchars_exec.
Require Import C.jet_elements_support_sha_be32_write C.jet_elements_support_sha_finalize_exec.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_input_hash_spec.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition eiu_hash_of (a : assetWith unit) (v : amountWith unit) (h : hash256) : hash256 :=
  sha256_bytes_of (elements_input_utxo_bytes (encode_asset a, encode_amount v) (from_hash256 h)).

Lemma eiu_asset_len a :
  length (map word8_array_value (elements_asset_bytes (encode_asset a))) = 33%nat.
Proof. rewrite map_length, elements_asset_bytes_length. reflexivity. Qed.

Lemma eiu_amount_len v :
  length (map word8_array_value (elements_amount_bytes (encode_amount v))) = 9%nat \/
  length (map word8_array_value (elements_amount_bytes (encode_amount v))) = 33%nat.
Proof.
  rewrite !map_length. destruct v as [x|[odd x] p]; [left|right];
    cbn [encode_amount elements_amount_bytes length]; rewrite vector_values_length; reflexivity.
Qed.

Lemma eiu_stream_regs bs :
  hash256_reg (sha256_bytes_of bs) =
    snd (absorb_i (fst (absorb_i [] sha256_iv_words (map word8_array_value bs)))
      (snd (absorb_i [] sha256_iv_words (map word8_array_value bs)))
      (sha_pad (Int64.repr (Z.of_nat (length bs))))).
Proof. exact (stream_hash_regs bs). Qed.

Section Payload.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eval_eiu_payload m bin ofs a v h :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  0 <= ofs -> ofs + 112 <= Ptrofs.max_unsigned ->
  bin <> bx -> bin <> bm ->
  asset_rep m bin (ofs + 32) a ->
  amount_rep m bin (ofs + 72) v ->
  uint32_array_at m bin ofs (hash256_reg h) ->
  exists ma mv mh mf vr,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 32))] E0 ma Vundef /\
    Clight2.eval_funcall sha_ge ma (Internal f_simplicity_sha256_confAmt)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 72))] E0 mv Vundef /\
    Clight2.eval_funcall sha_ge mv (Internal f_sha256_hash)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr ofs)] E0 mh Vundef /\
    Clight2.eval_funcall sha_ge mh (Internal f_sha256_finalize)
      [Vptr bx Ptrofs.zero] E0 mf vr /\
    (forall j, (j < 8)%nat ->
      Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg (eiu_hash_of a v h)) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k q, Mem.valid_block m b -> Mem.perm m b o k q -> Mem.perm mf b o k q) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC Ho HM Hbinx Hbinm HA HV HH.
  assert (Vbin : Mem.valid_block m bin).
  { destruct HA as [_ HP]. eapply load_valid_block; exact HP. }
  set (A := map word8_array_value (elements_asset_bytes (encode_asset a))).
  set (B := map word8_array_value (elements_amount_bytes (encode_amount v))).
  destruct (eval_sha256_asset_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm m [] sha256_iv_words
    Int64.zero false bin (ofs + 32) a HC ltac:(lia) Hbinx Hbinm HA)
    as (ma & CA & AX & LA & PA & VA).
  fold A in AX.
  assert (HAlen : length A = 33%nat) by apply eiu_asset_len.
  rewrite HAlen in AX.
  change (Int64.add Int64.zero (Int64.repr (Z.of_nat 33))) with (Int64.repr 33) in AX.
  assert (HV' : amount_rep ma bin (ofs + 72) v).
  { eapply amount_rep_mono; [exact HV|]. intros ch o w _ _ HL.
    rewrite LA; [exact HL|exact Vbin|exact Hbinx|exact Hbinm]. }
  destruct (eval_sha256_amount_repr Hmodel bx bm Hmx Hgx Hgm Hcx Hcm ma _ _
    (Int64.repr 33) _ bin (ofs + 72) v AX ltac:(lia) Hbinx Hbinm HV')
    as (mv & CV & VX & LV & PV & VV).
  fold A B in VX.
  rewrite <- !absorb_i_app in VX.
  assert (HH' : forall j, (j < 8)%nat ->
    Mem.load Mint32 mv bin (Ptrofs.unsigned (Ptrofs.repr ofs) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg h) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    rewrite LV by auto. rewrite LA by auto.
    apply HH, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mv bin (Ptrofs.repr ofs)
    _ _ (hash256_reg h) _ _ VX (hash256_len h)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HH')
    as (mh & CH & HX & LH & PH & VH).
  rewrite <- !absorb_i_app in HX.
  destruct (ctxi_finalize bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mh _ _ _ _ HX)
    as (mf & CF & RF & LF & PF & VF).
  assert (HB : length B = 9%nat \/ length B = 33%nat) by apply eiu_amount_len.
  assert (HS : (A ++ B) ++ be_bytes (hash256_reg h) =
    map word8_array_value
      (elements_input_utxo_bytes (encode_asset a, encode_amount v) (from_hash256 h))).
  { unfold A, B, elements_input_utxo_bytes, elements_asset_amount_bytes.
    rewrite !map_app, elements_hash_words_bytes. reflexivity. }
  exists ma, mv, mh, mf, (Vint (bit_int (negb
    (uc_overflow (jet_elements_conf_amount_exec.amt_overflow (Int64.repr 33)
      (jet_elements_confidential_exec.conf_overflow Int64.zero false (conf_prefix a)) (conf_prefix v))
      (Int64.add (Int64.repr 33) (Int64.repr (Z.of_nat (length B)))) (Int64.repr 32))))).
  split; [exact CA|]. split; [exact CV|]. split; [exact CH|]. split; [exact CF|].
  split.
  { unfold eiu_hash_of. rewrite eiu_stream_regs.
    rewrite HS in RF.
    assert (HCnt : Int64.add
       (Int64.add (Int64.repr 33) (Int64.repr (Z.of_nat (length B)))) (Int64.repr 32) =
      Int64.repr (Z.of_nat (length
        (elements_input_utxo_bytes (encode_asset a, encode_amount v) (from_hash256 h))))).
    { unfold elements_input_utxo_bytes, elements_asset_amount_bytes.
      rewrite !app_length, elements_asset_bytes_length, vector_values_length.
      unfold B in HB |- *. rewrite !map_length in HB |- *.
      cbn [fst snd]. destruct HB as [HB|HB]; rewrite HB; reflexivity. }
    rewrite HCnt in RF. exact RF. }
  split.
  { intros ch b o V Nx Nm. rewrite LF by auto. rewrite LH by auto.
    rewrite LV by auto. apply LA; assumption. }
  split.
  { intros b o k q V P. apply PF; [auto|]. apply PH; [auto|]. apply PV; [auto|].
    apply PA; assumption. }
  { intros b V. auto. }
Qed.
End Payload.
