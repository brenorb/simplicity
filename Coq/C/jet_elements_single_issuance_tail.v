(** Whole active-issuance suffix: proof hashes, present marker and the real
    tag-dispatched blinding/entropy branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_bitmachine_rep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_single_issuance_prep C.jet_elements_single_issuance_amount.
Require Import C.jet_elements_single_issuance_none C.jet_elements_single_issuance_blinding.
Require Import C.jet_elements_single_input_optional.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_elements_support_sha_ctxi.
Require Import C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_uchars_exec.
Require Import C.jet_elements_support_sha_be32_write.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.

Definition eis_active_tail : statement :=
  ltac:(let s := eval cbv delta [eis_some] beta iota in eis_some in
    lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?t))) => exact t end).

Lemma eis_active_tail_shape : eis_active_tail =
  Ssequence (eis_hash_stmt _assetRangeProofHash)
    (Ssequence (eis_hash_stmt _tokenRangeProofHash)
      (Ssequence (eih_uchar_stmt Int.one) eis_blinding_stmt)).
Proof. reflexivity. Qed.

Definition eis_tail_bytes (isnew : bool) (ha ht q ent : hash256) : list int :=
  ((be_bytes (hash256_reg ha) ++ be_bytes (hash256_reg ht)) ++ [Int.one]) ++
    eis_blinding_bytes isnew q ent.

Lemma eis_tail_bytes_length isnew ha ht q ent : length (eis_tail_bytes isnew ha ht q ent) = 129%nat.
Proof.
  unfold eis_tail_bytes. rewrite !app_length, !be_bytes_length, !hash256_len,
    eis_blinding_bytes_length. reflexivity.
Qed.

Section Tail.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem exec_eis_active_tail (isnew : bool) e le m bin ofs bb ha ht q ent l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  e!_ctx = Some (bx, CTX) -> e!___compound__3 = Some (bb, tarray tuchar 32) ->
  e!_sha256_uchars = None -> e!_sha256_hash = None -> e!_sha256_uchar = None ->
  le!_issuance = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned -> bin <> bx -> bin <> bm ->
  bb <> bin -> bb <> bx -> bb <> bm -> bb <> GC -> bb <> GM ->
  Mem.load Mint32 m bin (ofs + 272) = Some (Vint (eis_kind isnew)) ->
  uint32_array_at m bin (ofs + 104) (hash256_reg ha) ->
  uint32_array_at m bin (ofs + 136) (hash256_reg ht) ->
  uint32_array_at m bin ofs (hash256_reg q) ->
  (isnew = false -> uint32_array_at m bin (ofs + 72) (hash256_reg ent)) ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  exists mf ovf',
    Clight2.exec_stmt sha_ge e le m eis_active_tail E0
      (PTree.set _t'5 (Vint (eis_kind isnew)) le) mf Out_normal /\
    ctxi mf bx bm (fst (absorb_i l regs (eis_tail_bytes isnew ha ht q ent)))
      (snd (absorb_i l regs (eis_tail_bytes isnew ha ht q ent))) (Int64.add c (Int64.repr 129)) ovf' /\
    (forall ch b o, Mem.valid_block m b -> b <> bb -> b <> bx -> b <> bm ->
      Mem.load ch mf b o = Mem.load ch m b o) /\
    (forall b o k p, Mem.valid_block m b -> Mem.perm m b o k p -> Mem.perm mf b o k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HX HC HB HU HH H1 HI HO HM Hix Him Hbi Hbx Hbm Hbg Hbc HT HA HR HQ HE HP.
  assert (VB : Mem.valid_block m bin) by (eapply load_valid_block; exact HT).
  assert (HA0 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 104)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg ha) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia.
    apply HA, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel m bin (Ptrofs.repr (ofs + 104))
    _ _ (hash256_reg ha) _ _ HX (hash256_len ha)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HA0)
    as (ma & CA & XA & LA & PA & VA).
  assert (HRA : forall j, (j < 8)%nat ->
    Mem.load Mint32 ma bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 136)) + 4 * Z.of_nat j) =
      Some (Vint (nth j (hash256_reg ht) Int.zero))).
  { intros j Hj. rewrite Ptrofs.unsigned_repr by lia. rewrite LA by assumption.
    apply HR, nth_error_nth'. rewrite hash256_len. exact Hj. }
  destruct (ctxi_hash bx bm Hmx Hgx Hgm Hcx Hcm Hmodel ma bin (Ptrofs.repr (ofs + 136))
    _ _ (hash256_reg ht) _ _ XA (hash256_len ht)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) HRA)
    as (mr & CR & XR & LR & PR & VR).
  destruct (ctxi_uchar bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mr _ _ Int.one _ _ XR eq_refl)
    as (mu & CU & XU & LU & PU & VU).
  assert (LT : forall ch o, Mem.load ch mu bin o = Mem.load ch m bin o).
  { intros ch o. rewrite LU by auto. rewrite LR by auto. apply LA; assumption. }
  assert (HPU : Mem.range_perm mu bb 0 32 Cur Writable).
  { intros o P. assert (VBb : Mem.valid_block m bb).
    { eapply Mem.perm_valid_block; apply HP; exact P. }
    apply PU; [auto|]. apply PR; [auto|]. apply PA; [exact VBb|apply HP, P]. }
  destruct (exec_eis_blinding Hmodel bx bm Hmx Hgx Hgm Hcx Hcm isnew e le mu bin ofs bb q ent
    _ _ _ _ XU HC HB HU HH HI HO HM Hix Him Hbi Hbx Hbm Hbg Hbc
    ltac:(rewrite LT; exact HT)
    ltac:(intros j v HJ; rewrite LT; apply HQ, HJ)
    ltac:(intros E j v HJ; rewrite LT; apply (HE E), HJ) HPU)
    as (mf & vf & CF & XF & LF & PF & VF).
  rewrite <- !absorb_i_app, !Int64.add_assoc in XF.
  change (Int64.add (Int64.repr 32)
    (Int64.add (Int64.repr 32) (Int64.add (Int64.repr 1) (Int64.repr 64))))
    with (Int64.repr 129) in XF.
  exists mf, vf. split.
  { rewrite eis_active_tail_shape. eapply exec_Sseq_1 with
      (t1 := E0) (t2 := E0) (le1 := le) (m1 := ma).
    - eapply eis_hash_stmt_exec; [exact eis_asset_proof_offset|lia|lia|exact HO|exact HM|
        exact HH|exact HC|exact HI|exact CA].
    - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mr).
      + eapply eis_hash_stmt_exec; [exact eis_token_proof_offset|lia|lia|exact HO|exact HM|
          exact HH|exact HC|exact HI|exact CR].
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mu).
        * eapply eih_uchar_stmt_exec; [exact H1|exact HC|reflexivity|exact CU].
        * exact CF. }
  split.
  { unfold eis_tail_bytes. rewrite <- !app_assoc. exact XF. }
  split.
  { intros ch b o V Nb Nx Nm. rewrite LF by auto.
    rewrite LU by auto. rewrite LR by auto. apply LA; assumption. }
  split.
  { intros b o k p V P. apply PF; [auto|]. apply PU; [auto|].
    apply PR; [auto|]. apply PA; assumption. }
  intros b V. apply VF, VU, VR, VA, V.
Qed.
End Tail.
