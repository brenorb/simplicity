(** Complete original outpoint middle execution; the public jet lifecycle is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_readBit_layout C.jet_read8s_layout C.jet_elements_support_sha_ctx_abs C.jet_sha_ctx8_model.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_context_spec C.jet_nonce_context_shape C.jet_nonce_exec_effects C.jet_nonce_exec_calls.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Require Import C.jet_forwardBits_layout C.jet_elements_support_sha_transport C.jet_elements_sha_program C.jet_nonce_exec_prefix C.jet_outpoint_exec_shape.

Require Import C.jet_buffer_input C.jet_outpoint_exec_read C.jet_outpoint_exec_absorb C.jet_outpoint_exec_payload C.jet_outpoint_exec_frame_ops.

Require Import C.jet_outpoint_middle_common C.jet_outpoint_middle_pegin.

Section Middle.
Variable Hmodel : memcpy_model.
Variables bl bm bb bx bi : block.
Hypotheses (Hlx : bl <> bx) (Hlm : bl <> bm) (Hlg : bl <> GC) (Hlc : bl <> GM).
Hypotheses (Hbx : bb <> bx) (Hbm : bb <> bm) (Hbg : bb <> GC) (Hbc : bb <> GM) (Hlb : bl <> bb).
Hypotheses (Hil : bi <> bl) (Hib : bi <> bb) (Hix : bi <> bx) (Him : bi <> bm).
Hypotheses (Hmx : bm <> bx) (Hgx : GC <> bx) (Hgm : GC <> bm) (Hcx : GM <> bx) (Hcm : GM <> bm).
Let e := op_env bl bm bb bx.

Theorem op_middle_exec le m edge rc (a : Ty.tySem op_pegin_type)
    (h : Ty.tySem Word256) (ix : Ty.tySem Word32) l regs c ovf :
  0 <= rc -> rc + 545 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 36 Cur Writable ->
  frame_input_cells_at m bi edge rc (@encode (Ty.Prod op_pegin_type (Ty.Prod Word256 Word32)) (a, (h, ix))) ->
  ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m op_middle E0
      (PTree.set _t'2 (Vint (bit_int (op_bit a))) le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 545) /\
    ctx_abs mf bx bm (fst (absorb l regs (op_full_bytes a h ix))) (snd (absorb l regs (op_full_bytes a h ix)))
      (Int64.add (Int64.add c (Int64.repr (op_count a))) (Int64.repr 36))
      (uc_overflow (op_overflow ovf c a) (Int64.add c (Int64.repr (op_count a))) (Int64.repr 36)) /\
    nonce_effects m mf [bl; bb; bx; bm].
Proof.
  intros H0 HM HF PW PB HI HC.
  change (frame_input_cells_at m bi edge rc ((@encode op_pegin_type a) ++ @encode (Ty.Prod Word256 Word32) (h, ix))) in HI.
  apply frame_input_cells_at_app in HI. destruct HI as [HIP HIO].
  rewrite encode_length in HIO. change (Z.of_nat (bitSize op_pegin_type)) with 257 in HIO.
  destruct (op_pegin_exec Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb
    Hil Hib Hix Him Hmx Hgx Hgm Hcx Hcm le m edge rc a l regs c ovf H0 ltac:(lia) HF PW PB HIP HC)
    as (m1 & HPegin & HF1 & HC1 & E1).
  assert (HI1 : frame_input_cells_at m1 bi edge (rc + 257) (@encode (Ty.Prod Word256 Word32) (h, ix))).
  { eapply nonce_effects_input; [exact E1|cbn; intuition congruence|exact HIO]. }
  assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
  assert (PB1 : Mem.range_perm m1 bb 0 36 Cur Writable).
  { intros ofs HO. apply (nonce_perms _ _ _ E1), PB, HO. }
  set (xs := op_outpoint_bytes h ix).
  assert (HL : Z.of_nat (length xs) = 36) by apply op_outpoint_bytes_length.
  assert (HI1' : frame_input_cells_at m1 bi edge (rc + 257) (concat (map (@encode Word8) xs))).
  { unfold xs. rewrite op_outpoint_encoding. exact HI1. }
  set (le1 := PTree.set _t'2 (Vint (bit_int (op_bit a))) le).
  destruct (op_payload_exec Hmodel le1 m1 bl bm bb bx bi edge (rc + 257) 36 xs
    (fst (absorb l regs (op_bytes a))) (snd (absorb l regs (op_bytes a)))
    (Int64.add c (Int64.repr (op_count a))) (op_overflow ovf c a)
    HL ltac:(lia) Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb ltac:(congruence) ltac:(congruence)
    Hmx Hgx Hgm Hcx Hcm ltac:(lia) ltac:(lia) HF1 PW1 PB1 HI1' HC1)
    as (mf & HPayload & HFields & HCtx & E2).
  replace (rc + 257 + 8 * 36) with (rc + 545) in HFields by lia.
  rewrite absorb_app in HCtx.
  exists mf. split.
  - unfold op_middle. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); eassumption.
  - split; [exact HFields|]. split; [exact HCtx|]. eapply nonce_effects_trans; eassumption.
Qed.
End Middle.

Lemma op_middle_then e le m le' m' le'' mf rest out :
  Clight2.exec_stmt elements_ge e le m op_middle E0 le' m' Out_normal ->
  Clight2.exec_stmt elements_ge e le' m' rest E0 le'' mf out ->
  Clight2.exec_stmt elements_ge e le m
    (Ssequence op_pegin (Ssequence (op_read 36) (Ssequence (op_absorb 36) rest))) E0 le'' mf out.
Proof.
  intros HS HR. unfold op_middle in HS.
  destruct (op_seq_normal_inv _ _ _ _ _ _ _ _ HS) as (le1 & m1 & H1 & H23).
  destruct (op_seq_normal_inv _ _ _ _ _ _ _ _ H23) as (le2 & m2 & H2 & H3).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); [exact H1|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le2); [exact H2|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m') (le1 := le'); eassumption.
Qed.
