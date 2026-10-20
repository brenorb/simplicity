(** Entire original asset/amount middle phase; not the full frame-jet lifecycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_readBit_layout C.jet_read8s_layout.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_sha_ctx8_model C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_transport C.jet_elements_support_sha_block_local C.jet_elements_sha_program.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_context_shape C.jet_nonce_exec_effects C.jet_nonce_exec_calls.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge sha_ge ge0.
Set Default Timeout 10.

Require Import C.jet_nonce_exec_payload C.jet_asset_exec_shape.

Require Import C.jet_forwardBits_layout C.jet_nonce_context_spec C.jet_nonce_exec_prefix.

Require Import C.jet_amount_exec_common C.jet_amount_exec_phase C.jet_amount_exec_seq C.jet_asset_exec_asset C.jet_nonce_exec_phase.

Definition asset_amount_middle :=
  Ssequence asset_prefix (Ssequence nc_readbytes (Ssequence nc_uchars amount_phase)).
Definition asset_overflow ovf c :=
  uc_overflow (uc_overflow ovf c (Int64.repr 1)) (Int64.add c (Int64.repr 1)) (Int64.repr 32).

Section Compose.
Variable Hmodel : memcpy_model.
Variables bl bm bb bx bi : block.
Hypotheses (Hlx : bl <> bx) (Hlm : bl <> bm) (Hlg : bl <> GC) (Hlc : bl <> GM).
Hypotheses (Hbx : bb <> bx) (Hbm : bb <> bm) (Hbg : bb <> GC) (Hbc : bb <> GM) (Hlb : bl <> bb).
Hypotheses (Hil : bi <> bl) (Hib : bi <> bb) (Hix : bi <> bx) (Him : bi <> bm).
Hypotheses (Hmx : bm <> bx) (Hgx : GC <> bx) (Hgm : GC <> bm) (Hcx : GM <> bx) (Hcm : GM <> bm).
Let e := nc_env bl bm bb bx.

Theorem asset_amount_middle_exec le m edge rc (p : Ty.tySem nonce_conf_type)
    (a : Ty.tySem amount_value_type) l regs c ovf :
  0 <= rc -> rc + 516 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  frame_input_cells_at m bi edge rc (@encode (Ty.Prod nonce_conf_type amount_value_type) (p, a)) ->
  ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m asset_amount_middle E0
      (amount_temps a (nonce_present_temps p le)) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 516) /\
    ctx_abs mf bx bm (fst (absorb l regs (asset_bytes p ++ amount_bytes a)))
      (snd (absorb l regs (asset_bytes p ++ amount_bytes a)))
      (Int64.add (Int64.add c (Int64.repr 33)) (Int64.repr (amount_count a)))
      (amount_overflow (asset_overflow ovf c) (Int64.add c (Int64.repr 33)) a) /\
    nonce_effects m mf [bl; bb; bx; bm].
Proof.
  intros H0 HM HF PW PB HI HC.
  change (frame_input_cells_at m bi edge rc ((@encode nonce_conf_type p) ++ @encode amount_value_type a)) in HI.
  apply frame_input_cells_at_app in HI. destruct HI as [HIP HIA].
  rewrite encode_length in HIA. change (Z.of_nat (bitSize nonce_conf_type)) with 258 in HIA.
  destruct (asset_phase_exec Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb
    Hil Hib Hix Him Hmx Hgx Hgm Hcx Hcm le m edge rc p l regs c ovf
    H0 ltac:(lia) HF PW PB HIP HC) as (m1 & HAsset & HF1 & HC1 & E1).
  assert (HI1 : frame_input_cells_at m1 bi edge (rc + 258) (@encode amount_value_type a)).
  { eapply nonce_effects_input; [exact E1|cbn; intuition congruence|exact HIA]. }
  assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
  assert (PB1 : Mem.range_perm m1 bb 0 32 Cur Writable).
  { intros ofs HO. apply (nonce_perms _ _ _ E1), PB, HO. }
  set (le1 := nonce_present_temps p le).
  destruct (amount_phase_exec Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb
    Hil Hib Hix Him Hmx Hgx Hgm Hcx Hcm le1 m1 edge (rc + 258) a
    (fst (absorb l regs (asset_bytes p))) (snd (absorb l regs (asset_bytes p)))
    (Int64.add c (Int64.repr 33)) (asset_overflow ovf c)
    ltac:(lia) ltac:(lia) HF1 PW1 PB1 HI1 HC1)
    as (mf & HAmount & HFields & HCtx & E2).
  replace (rc + 258 + 258) with (rc + 516) in HFields by lia.
  rewrite absorb_app in HCtx.
  destruct (amount_seq_normal_inv _ _ _ _ _ _ _ _ HAsset) as (leP & mp & HPrefix & HRest).
  destruct (amount_seq_normal_inv _ _ _ _ _ _ _ _ HRest) as (leR & mr & HRead & HAdd).
  exists mf. split.
  - unfold asset_amount_middle. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mp) (le1 := leP); [exact HPrefix|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := leR); [exact HRead|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); eassumption.
  - split; [exact HFields|]. split; [exact HCtx|]. eapply nonce_effects_trans; eassumption.
Qed.
End Compose.

Lemma asset_amount_middle_then e le m le' m' le'' mf rest out :
  Clight2.exec_stmt elements_ge e le m asset_amount_middle E0 le' m' Out_normal ->
  Clight2.exec_stmt elements_ge e le' m' rest E0 le'' mf out ->
  Clight2.exec_stmt elements_ge e le m
    (Ssequence asset_prefix (Ssequence nc_readbytes (Ssequence nc_uchars (Ssequence amount_phase rest))))
    E0 le'' mf out.
Proof.
  intros HS HR. unfold asset_amount_middle in HS.
  destruct (amount_seq_normal_inv _ _ _ _ _ _ _ _ HS) as (le1 & m1 & H1 & H23).
  destruct (amount_seq_normal_inv _ _ _ _ _ _ _ _ H23) as (le2 & m2 & H2 & H34).
  destruct (amount_seq_normal_inv _ _ _ _ _ _ _ _ H34) as (le3 & m3 & H3 & H4).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); [exact H1|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le2); [exact H2|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := le3); [exact H3|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m') (le1 := le'); eassumption.
Qed.
