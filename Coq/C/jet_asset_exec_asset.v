(** Original asset prefix and payload phase; not the complete asset_amount_hash jet. *)
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

Require Import C.jet_nonce_exec_prefix.

Require Import C.jet_buffer_input C.jet_asset_exec_prefix C.jet_asset_exec_shape C.jet_nonce_exec_phase C.jet_nonce_exec_payload.

Definition asset_prefix_value (p : Ty.tySem nonce_conf_type) : Ty.tySem Word8 * Ty.tySem Word256 :=
  match p with
  | inl (odd, h) => (nonce_byte (match odd with inl _ => 10 | inr _ => 11 end), h)
  | inr h => (nonce_byte 1, h)
  end.
Definition asset_bytes p :=
  fst (asset_prefix_value p) :: vector_values Word8 5 (snd (asset_prefix_value p)).

Lemma asset_prefix_machine :
  word8_array_value (nonce_byte 10) = Int.repr 10 /\
  word8_array_value (nonce_byte 11) = Int.repr 11.
Proof. vm_compute; split; reflexivity. Qed.

Lemma asset_bytes_length p : length (asset_bytes p) = 33%nat.
Proof.
  unfold asset_bytes. cbn [length].
  exact (f_equal S (vector_values_length (Word 3) 5 (snd (asset_prefix_value p)))).
Qed.

Section Asset.
Variable Hmodel : memcpy_model.
Variables bl bm bb bx bi : block.
Hypotheses (Hlx : bl <> bx) (Hlm : bl <> bm) (Hlg : bl <> GC) (Hlc : bl <> GM).
Hypotheses (Hbx : bb <> bx) (Hbm : bb <> bm) (Hbg : bb <> GC) (Hbc : bb <> GM) (Hlb : bl <> bb).
Hypotheses (Hil : bi <> bl) (Hib : bi <> bb) (Hix : bi <> bx) (Him : bi <> bm).
Hypotheses (Hmx : bm <> bx) (Hgx : GC <> bx) (Hgm : GC <> bm) (Hcx : GM <> bx) (Hcm : GM <> bm).
Let e := nc_env bl bm bb bx.

Lemma asset_prefix_exec le m edge rc (p : Ty.tySem nonce_conf_type) l regs c ovf :
  0 <= rc -> rc + 258 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  frame_input_cells_at m bi edge rc (@encode nonce_conf_type p) -> ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m asset_prefix E0 (nonce_present_temps p le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 2) /\
    frame_input_cells_at mf bi edge (rc + 2) (@encode Word256 (snd (asset_prefix_value p))) /\
    ctx_abs mf bx bm (fst (absorb l regs [fst (asset_prefix_value p)]))
      (snd (absorb l regs [fst (asset_prefix_value p)]))
      (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1)) /\
    nonce_effects m mf [bl; bx; bm].
Proof.
  intros H0 HM HF PW HI HC. destruct p as [[[[]|[]] h]|h].
  - exact (tagged_confidential_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      _t'3 _t'2 10 11 (proj1 asset_prefix_machine) (proj2 asset_prefix_machine)
      le m edge rc false h l regs c ovf H0 HM HF PW HI HC).
  - exact (tagged_confidential_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      _t'3 _t'2 10 11 (proj1 asset_prefix_machine) (proj2 asset_prefix_machine)
      le m edge rc true h l regs c ovf H0 HM HF PW HI HC).
  - exact (tagged_explicit_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      _t'3 _t'2 10 11 le m edge rc h l regs c ovf H0 HM HF PW HI HC).
Qed.

Theorem asset_phase_exec le m edge rc (p : Ty.tySem nonce_conf_type) l regs c ovf :
  0 <= rc -> rc + 258 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  frame_input_cells_at m bi edge rc (@encode nonce_conf_type p) -> ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m asset_phase E0 (nonce_present_temps p le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 258) /\
    ctx_abs mf bx bm (fst (absorb l regs (asset_bytes p))) (snd (absorb l regs (asset_bytes p)))
      (Int64.add c (Int64.repr 33))
      (uc_overflow (uc_overflow ovf c (Int64.repr 1)) (Int64.add c (Int64.repr 1)) (Int64.repr 32)) /\
    nonce_effects m mf [bl; bb; bx; bm].
Proof.
  intros H0 HM HF PW PB HI HC.
  destruct (asset_prefix_exec le m edge rc p l regs c ovf H0 HM HF PW HI HC)
    as (m1 & HPrefix & HF1 & HI1 & HC1 & E1).
  set (le1 := nonce_present_temps p le).
  assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
  assert (PB1 : Mem.range_perm m1 bb 0 32 Cur Writable).
  { intros ofs HO. apply (nonce_perms _ _ _ E1), PB, HO. }
  destruct (nonce_payload_exec Hmodel le1 m1 bl bm bb bx bi edge (rc + 2) (snd (asset_prefix_value p))
    (fst (absorb l regs [fst (asset_prefix_value p)]))
    (snd (absorb l regs [fst (asset_prefix_value p)]))
    (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1))
    Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb ltac:(congruence) ltac:(congruence)
    Hmx Hgx Hgm Hcx Hcm ltac:(lia) ltac:(lia) HF1 PW1 PB1 HI1 HC1)
    as (mf & HPayload & HFields & HCtx & E2).
  replace (rc + 2 + 256) with (rc + 258) in HFields by lia.
  rewrite absorb_app, nonce_counter_one_then_32 in HCtx.
  exists mf. split.
  - unfold asset_phase. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); eassumption.
  - split; [exact HFields|]. split; [exact HCtx|].
    eapply nonce_effects_trans; [|exact E2].
    eapply nonce_effects_mono; [exact E1|]. intros b H. clear -H. cbn in H |- *. tauto.
Qed.
End Asset.
