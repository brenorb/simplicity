(** Concrete optional-hash and u32 SHA calls needed by input_hash.
    The optional path reads no payload for None. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_readBit_layout.
Require Import C.jet_read8s_layout C.jet_uint32_array_init C.jet_buffer_input C.jet_bitcoin_tx_hash.
Require Import C.jets_elements C.jet_elements_conf_hash_bridge C.jet_elements_input_utxo_payload.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_u32be_exec.
Require Import C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_be32_write.
Require Import C.jet_elements_support_sha_uchars_exec.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition eih_optional_bytes (h : option hash256) : list int :=
  match h with None => [Int.zero] | Some h => Int.one :: be_bytes (hash256_reg h) end.

Lemma eih_optional_bytes_canonical h :
  eih_optional_bytes h = map word8_array_value
    (annex_elem_bytes (match h with None => inl tt | Some h => inr (from_hash256 h) end)).
Proof.
  destruct h as [h|]; [|reflexivity].
  change (Int.one :: be_bytes (hash256_reg h) =
    Int.one :: map word8_array_value (vector_values Word8 5 (from_hash256 h))).
  rewrite elements_hash_words_bytes. reflexivity.
Qed.

Definition eih_optional_calls (bx bin : block) (ofs : Z) (h : option hash256)
    (m mf : mem) : Prop :=
  match h with
  | None => exists vr, Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
      [Vptr bx Ptrofs.zero; Vint Int.zero] E0 mf vr
  | Some _ => exists mi vr,
      Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
        [Vptr bx Ptrofs.zero; Vint Int.one] E0 mi vr /\
      Clight2.eval_funcall sha_ge mi (Internal f_sha256_hash)
        [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr ofs)] E0 mf Vundef
  end.

Section Calls.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eih_ctxi_u32be m l regs (x : int64) c ovf :
  ctxi m bx bm l regs c ovf ->
  let ovf' := uc_overflow ovf c (Int64.repr 4) in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u32be)
      [Vptr bx Ptrofs.zero; Vlong x] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxi m' bx bm (fst (absorb_i l regs (c_be32_bytes x))) (snd (absorb_i l regs (c_be32_bytes x)))
      (Int64.add c (Int64.repr 4)) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_u32be Hmodel m bx 0 bm 0 l regs c x ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hr HOut HCnt HMod HOvf HBlk
    (ctxi_regs_access bx bm Hmx Hgx Hgm Hcx Hcm _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm bx bm Hmx Hgx Hgm Hcx Hcm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step bx bm Hmx Hgx Hgm Hcx Hcm m m' l regs c ovf (c_be32_bytes x) 4 ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615; lia)
    eq_refl HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|].
  split; [exact HL'|]. split; [exact HPerm'|exact HVal'].
Qed.

Theorem eval_eih_optional_hash m bin ofs (h : option hash256) l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  0 <= ofs -> ofs + 32 <= Ptrofs.max_unsigned ->
  bin <> bx -> bin <> bm ->
  (forall h0, h = Some h0 -> uint32_array_at m bin ofs (hash256_reg h0)) ->
  exists mf ovf',
    eih_optional_calls bx bin ofs h m mf /\
    ctxi mf bx bm (fst (absorb_i l regs (eih_optional_bytes h)))
      (snd (absorb_i l regs (eih_optional_bytes h)))
      (Int64.add c (Int64.repr (Z.of_nat (length (eih_optional_bytes h))))) ovf' /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC Ho HM Hbinx Hbinm HH. destruct h as [h|].
  - destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m l regs Int.one c ovf HC eq_refl)
      as (mi & CU & UX & LU & PU & VU).
    assert (Vbin : Mem.valid_block m bin).
    { assert (HL0 : Mem.load Mint32 m bin (ofs + 4 * Z.of_nat 0) =
        Some (Vint (nth 0 (hash256_reg h) Int.zero))).
      { apply HH with (h0 := h); [reflexivity|].
        apply nth_error_nth'. rewrite hash256_len. exact (Nat.lt_0_succ 7). }
      eapply load_valid_block; exact HL0. }
    assert (HH' : forall j, (j < 8)%nat ->
      Mem.load Mint32 mi bin (Ptrofs.unsigned (Ptrofs.repr ofs) + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg h) Int.zero))).
    { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
      rewrite LU by assumption. apply HH with (h0 := h); [reflexivity|].
      apply nth_error_nth'. rewrite hash256_len. exact Hj. }
    destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mi bin (Ptrofs.repr ofs)
      _ _ (hash256_reg h) _ _ UX (hash256_len h)
      ltac:(rewrite Ptrofs.unsigned_repr by lia; exact HM) HH')
      as (mf & CH & HX & LH & PH & VH).
    rewrite <- absorb_i_app in HX.
    rewrite Int64.add_assoc in HX.
    change (Int64.add (Int64.repr 1) (Int64.repr 32)) with (Int64.repr 33) in HX.
    match type of HX with ctxi _ _ _ _ _ _ ?flag => exists mf, flag end.
    split; [exists mi; eexists; split; [exact CU|exact CH]|].
    split.
    { assert (HB : length (eih_optional_bytes (Some h)) = 33%nat).
      { change (S (length (be_bytes (hash256_reg h))) = 33%nat).
        rewrite be_bytes_length, hash256_len. reflexivity. }
      rewrite HB. exact HX. }
    split.
    { intros ch b o V Nx Nm. rewrite LH by auto. apply LU; assumption. }
    split.
    { intros b o k p V P. apply PH; [apply VU; exact V|apply PU; assumption]. }
    intros b V. apply VH, VU, V.
  - destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m l regs Int.zero c ovf HC eq_refl)
      as (mf & CU & HX & LH & PH & VH).
    match type of HX with ctxi _ _ _ _ _ _ ?flag => exists mf, flag end.
    split; [eexists; exact CU|].
    split; [exact HX|]. split; [exact LH|]. split; assumption.
Qed.
End Calls.
