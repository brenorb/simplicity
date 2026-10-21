(** Confidential hashing from the same memory representations used by the
    registered Elements getters, into canonical serializer bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init.
Require Import C.jets_elements C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_amount_jets.
Require Import C.jet_elements_asset_amount_hash_spec C.jet_read8s_layout.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_confidential_exec.
Require Import C.jet_elements_support_sha_uchars_prep Simplicity.Digest.
Require Import C.jet_elements_confidential_wrap C.jet_elements_conf_amount_exec C.jet_elements_conf_hash_bridge.
Import Ctypes Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.

Section Represented.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eval_sha256_asset_repr m l regs c ovf bc oc (a : assetWith unit) :
  ctxi m bx bm l regs c ovf ->
  0 <= oc /\ oc + 36 <= Ptrofs.max_unsigned ->
  bc <> bx -> bc <> bm -> asset_rep m bc oc a ->
  let B := map word8_array_value (elements_asset_bytes (encode_asset a)) in
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAsset)
      [Vptr bx (Ptrofs.repr 0); Vptr bc (Ptrofs.repr oc)] E0 mf Vundef /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr (Z.of_nat (length B)))) (conf_overflow c ovf (conf_prefix a)) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch mf b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC HO Hbx Hbm [HW HP] B.
  unfold B. rewrite <- elements_asset_canonical_bytes.
  apply (eval_sha256_confAsset Hmodel bx bm l regs c ovf Hmx Hgx Hgm Hcx Hcm
    bc oc (asset_words a) HO (asset_words_length a) Hbx Hbm m (conf_prefix a) HC HP).
  - destruct a as [h|[odd h] p].
    + right; left; reflexivity.
    + destruct odd; [right; right; right; reflexivity|right; right; left; reflexivity].
  - intros _ j Hj. apply HW. apply nth_error_nth'; rewrite asset_words_length; exact Hj.
Qed.

Theorem eval_sha256_amount_repr m l regs c ovf ba oa (a : amountWith unit) :
  ctxi m bx bm l regs c ovf ->
  0 <= oa /\ oa + 40 <= Ptrofs.max_unsigned ->
  ba <> bx -> ba <> bm -> amount_rep m ba oa a ->
  let B := map word8_array_value (elements_amount_bytes (encode_amount a)) in
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confAmt)
      [Vptr bx (Ptrofs.repr 0); Vptr ba (Ptrofs.repr oa)] E0 mf Vundef /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr (Z.of_nat (length B)))) (amt_overflow c ovf (conf_prefix a)) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch mf b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC HO Hbx Hbm [HW HP] B.
  unfold B. rewrite <- elements_amount_canonical_bytes.
  apply (eval_sha256_confAmt Hmodel bx bm l regs c ovf Hmx Hgx Hgm Hcx Hcm
    ba oa (amount_words a) (amount_value a) HO (amount_words_length a) Hbx Hbm m (conf_prefix a) HC HP).
  destruct a as [v|[odd h] p].
  - left. split; [reflexivity|exact HW].
  - right. split.
    + destruct odd; cbn [conf_prefix]; auto.
    + intros j Hj. apply HW. apply nth_error_nth'; rewrite amount_words_length; exact Hj.
Qed.
End Represented.
