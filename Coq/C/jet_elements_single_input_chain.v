(** Actual optional-pegin/outpoint/sequence/annex/finalize SHA chain.
    Both optional hashes preserve unread payload freedom when absent. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_readBit_layout.
Require Import C.jet_read8s_layout.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_buffer_input.
Require Import C.jet_bitcoin_input_hash_spec C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_composite_hash.
Require Import C.jets_elements C.jet_elements_prim C.jet_elements_conf_hash_bridge.
Require Import C.jet_elements_input_utxo_payload C.jet_elements_outpoints_hash_program.
Require Import C.jet_elements_single_input_hash_spec C.jet_elements_single_input_payload.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_be32_write.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Definition eih_hash_of pg (op : outpoint) (sq : int) ax :=
  sha256_bytes_of (elements_single_input_bytes
    (match pg with None => inl tt | Some h => inr (from_hash256 h) end)
    (from_hash256 (opHash op), @fromZ (WordToZ 5) (Int.unsigned (opIndex op)))
    (@fromZ (WordToZ 5) (Int.unsigned sq))
    (match ax with None => inl tt | Some h => inr (from_hash256 h) end)).

Lemma eih_optional_length h : length (eih_optional_bytes h) = 1%nat \/
  length (eih_optional_bytes h) = 33%nat.
Proof.
  destruct h as [h|]; [right|left; reflexivity].
  change (S (length (be_bytes (hash256_reg h))) = 33%nat).
  rewrite be_bytes_length, hash256_len. reflexivity.
Qed.

Section Chain.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eval_eih_payload m bin ofs pg (op : outpoint) sq ax :
  ctxi m bx bm [] sha256_iv_words Int64.zero false ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  bin <> bx -> bin <> bm ->
  (forall h, pg = Some h -> uint32_array_at m bin (ofs + 32) (hash256_reg h)) ->
  uint32_array_at m bin (ofs + 96) (hash256_reg (opHash op)) ->
  (forall h, ax = Some h -> uint32_array_at m bin ofs (hash256_reg h)) ->
  exists mP mH mI mS mA mf vI vS vF,
    eih_optional_calls bx bin (ofs + 32) pg m mP /\
    Clight2.eval_funcall sha_ge mP (Internal f_sha256_hash)
      [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 96))] E0 mH Vundef /\
    Clight2.eval_funcall sha_ge mH (Internal f_sha256_u32be)
      [Vptr bx Ptrofs.zero; Vlong (Int64.repr (Int.unsigned (opIndex op)))] E0 mI vI /\
    Clight2.eval_funcall sha_ge mI (Internal f_sha256_u32be)
      [Vptr bx Ptrofs.zero; Vlong (Int64.repr (Int.unsigned sq))] E0 mS vS /\
    eih_optional_calls bx bin ofs ax mS mA /\
    Clight2.eval_funcall sha_ge mA (Internal f_sha256_finalize)
      [Vptr bx Ptrofs.zero] E0 mf vF /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mH b o = Mem.load ch m b o) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mI b o = Mem.load ch m b o) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mS b o = Mem.load ch m b o) /\
    (forall j, (j < 8)%nat ->
      Mem.load Mint32 mf bm (0 + 4 * Z.of_nat j) =
        Some (Vint (nth j (hash256_reg (eih_hash_of pg op sq ax)) Int.zero))) /\
    (forall ch b o, Mem.valid_block m b -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC Ho HM Hbinx Hbinm HPG HOP HAX.
  assert (Vbin : Mem.valid_block m bin).
  { assert (HL0 : Mem.load Mint32 m bin (ofs + 96 + 4 * Z.of_nat 0) =
      Some (Vint (nth 0 (hash256_reg (opHash op)) Int.zero))).
    { apply HOP, nth_error_nth'. rewrite hash256_len. lia. }
    eapply load_valid_block; exact HL0. }
  destruct (eval_eih_optional_hash Hmodel bx bm Hmx Hgx Hgm Hcx Hcm m bin (ofs + 32)
    pg [] sha256_iv_words Int64.zero false HC ltac:(lia) ltac:(lia) Hbinx Hbinm HPG)
    as (mP & ovfP & CP & PX & LP & PP & VP).
  assert (HOP' : forall j, (j < 8)%nat ->
    Mem.load Mint32 mP bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 96)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg (opHash op)) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia. rewrite LP by assumption.
    apply HOP, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mP bin (Ptrofs.repr (ofs + 96))
    _ _ (hash256_reg (opHash op)) _ _ PX (hash256_len (opHash op))
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HOP')
    as (mH & CH & HX & LH & PH & VH).
  destruct (eih_ctxi_u32be Hmodel bx bm Hmx Hgx Hgm Hcx Hcm mH _ _
    (Int64.repr (Int.unsigned (opIndex op))) _ _ HX)
    as (mI & CI & IX & LI & PI & VI).
  destruct (eih_ctxi_u32be Hmodel bx bm Hmx Hgx Hgm Hcx Hcm mI _ _
    (Int64.repr (Int.unsigned sq)) _ _ IX)
    as (mS & CS & SX & LS & PS & VS).
  assert (HAX' : forall h, ax = Some h -> uint32_array_at mS bin ofs (hash256_reg h)).
  { intros h E j v Hj.
    rewrite LS by (auto using VP, VH, VI). rewrite LI by (auto using VP, VH).
    rewrite LH by auto. rewrite LP by assumption. exact (HAX h E j v Hj). }
  destruct (eval_eih_optional_hash Hmodel bx bm Hmx Hgx Hgm Hcx Hcm mS bin ofs
    ax _ _ _ _ SX Ho ltac:(lia) Hbinx Hbinm HAX')
    as (mA & ovfA & CA & AX & LA & PA & VA).
  rewrite <- !absorb_i_app in AX.
  destruct (ctxi_finalize bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mA _ _ _ _ AX)
    as (mf & CF & RF & LF & PF & VF).
  set (bs := elements_single_input_bytes
    (match pg with None => inl tt | Some h => inr (from_hash256 h) end)
    (from_hash256 (opHash op), @fromZ (WordToZ 5) (Int.unsigned (opIndex op)))
    (@fromZ (WordToZ 5) (Int.unsigned sq))
    (match ax with None => inl tt | Some h => inr (from_hash256 h) end)).
  assert (HB : (((eih_optional_bytes pg ++ be_bytes (hash256_reg (opHash op))) ++
    c_be32_bytes (Int64.repr (Int.unsigned (opIndex op)))) ++
    c_be32_bytes (Int64.repr (Int.unsigned sq))) ++ eih_optional_bytes ax =
    map word8_array_value bs).
  { unfold bs, elements_single_input_bytes, elements_outpoint_bytes. cbn [fst snd].
    rewrite !map_app, <- !eih_optional_bytes_canonical, <- elements_hash_words_bytes,
      <- !be32_bytes_word. rewrite !app_assoc. reflexivity. }
  rewrite <- !app_assoc in HB. rewrite HB in RF.
  assert (HCnt : Int64.add
    (Int64.add
      (Int64.add
        (Int64.add (Int64.add Int64.zero (Int64.repr (Z.of_nat (length (eih_optional_bytes pg)))))
          (Int64.repr 32)) (Int64.repr 4)) (Int64.repr 4))
    (Int64.repr (Z.of_nat (length (eih_optional_bytes ax)))) =
    Int64.repr (Z.of_nat (length bs))).
  { assert (HL : length bs = (length (eih_optional_bytes pg) + 32 + 4 + 4 +
       length (eih_optional_bytes ax))%nat).
    { apply (f_equal (@length int)) in HB.
      rewrite !app_length, map_length, be_bytes_length, hash256_len in HB.
      change (length (c_be32_bytes (Int64.repr (Int.unsigned (opIndex op))))) with 4%nat in HB.
      change (length (c_be32_bytes (Int64.repr (Int.unsigned sq)))) with 4%nat in HB.
      lia. }
    rewrite HL. destruct (eih_optional_length pg) as [HP|HP];
      destruct (eih_optional_length ax) as [HA|HA]; rewrite HP, HA; reflexivity. }
  rewrite HCnt in RF.
  match type of CI with Clight2.eval_funcall _ _ _ _ _ _ ?ri =>
    match type of CS with Clight2.eval_funcall _ _ _ _ _ _ ?rs =>
      match type of CF with Clight2.eval_funcall _ _ _ _ _ _ ?rf =>
        exists mP, mH, mI, mS, mA, mf, ri, rs, rf end end end.
  split; [exact CP|]. split; [exact CH|]. split; [exact CI|]. split; [exact CS|].
  split; [exact CA|]. split; [exact CF|].
  split.
  { intros ch b o V Nx Nm. rewrite LH by auto. apply LP; assumption. }
  split.
  { intros ch b o V Nx Nm. rewrite LI by (auto using VP, VH).
    rewrite LH by auto. apply LP; assumption. }
  split.
  { intros ch b o V Nx Nm. rewrite LS by (auto using VP, VH, VI).
    rewrite LI by (auto using VP, VH). rewrite LH by auto. apply LP; assumption. }
  split.
  { unfold eih_hash_of. fold bs. rewrite eiu_stream_regs. exact RF. }
  assert (Vms_all : forall b, Mem.valid_block m b -> Mem.valid_block mS b).
  { intros b V. apply VS, VI, VH, VP, V. }
  assert (Vma_all : forall b, Mem.valid_block m b -> Mem.valid_block mA b).
  { intros b V. apply VA, Vms_all, V. }
  split.
  { intros ch b o V Nx Nm.
    rewrite LF by (auto using Vma_all).
    rewrite LA by (auto using Vms_all).
    rewrite LS by (auto using VP, VH, VI). rewrite LI by (auto using VP, VH).
    rewrite LH by auto. apply LP; assumption. }
  split.
  { intros b o k p V P.
    apply PF; [auto using Vma_all|].
    apply PA; [auto using Vms_all|].
    apply PS; [auto using VP, VH, VI|]. apply PI; [auto using VP, VH|].
    apply PH; [auto|]. apply PP; assumption. }
  intros b V. apply VF, VA, VS, VI, VH, VP, V.
Qed.
End Chain.
