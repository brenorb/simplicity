(** Reusable confidential tagged-word Clight prefixes with explicit byte parameters. *)
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
Local Opaque elements_ge C.jet_elements_support_sha_linkage.sha_ge.
Set Default Timeout 10.

Require Import C.jet_nonce_exec_prefix.

Definition tagged_prefix (itag iparity : ident) (z0 z1 : Z) : statement :=
  Ssequence (nc_readbit itag)
    (Sifthenelse (Etempvar itag tbool) (Ssequence nc_forward (nc_uchar 1))
      (Ssequence (nc_readbit iparity)
        (Sifthenelse (Etempvar iparity tbool) (nc_uchar z1) (nc_uchar z0)))).

Section TaggedPrefix.
Variable Hmodel : memcpy_model.
Variables bl bm bb bx bi : block.
Hypotheses (Hlx : bl <> bx) (Hlm : bl <> bm) (Hlg : bl <> GC) (Hlc : bl <> GM).
Hypotheses (Hil : bi <> bl) (Hix : bi <> bx) (Him : bi <> bm).
Hypotheses (Hmx : bm <> bx) (Hgx : GC <> bx) (Hgm : GC <> bm) (Hcx : GM <> bx) (Hcm : GM <> bm).
Variables (itag iparity : ident) (z0 z1 : Z).
Hypotheses (HZ0 : word8_array_value (nonce_byte z0) = Int.repr z0)
           (HZ1 : word8_array_value (nonce_byte z1) = Int.repr z1).
Let e := nc_env bl bm bb bx.

Theorem tagged_explicit_prefix le m edge rc (h : Ty.tySem Word256) l regs c ovf :
  0 <= rc -> rc + 258 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  frame_input_cells_at m bi edge rc (@encode nonce_conf_type (inr h)) ->
  ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m (tagged_prefix itag iparity z0 z1) E0
      (PTree.set itag (Vint Int.one) le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 2) /\
    frame_input_cells_at mf bi edge (rc + 2) (@encode Word256 h) /\
    ctx_abs mf bx bm (fst (absorb l regs [nonce_byte 1])) (snd (absorb l regs [nonce_byte 1]))
      (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1)) /\
    nonce_effects m mf [bl; bx; bm].
Proof.
  intros H0 HM HF PW HI HC.
  change (frame_input_cells_at m bi edge rc (Some true :: None :: encode h)) in HI.
  destruct (nonce_read_cell bl bm bb bx bi Hlx Hlm Hlg Hlc Hil le m edge rc true (None :: encode h) l regs c ovf itag
    ltac:(lia) HF PW HI HC) as (m1 & HRead & HF1 & HI1 & HC1 & E1).
  set (le1 := PTree.set itag (Vint Int.one) le).
  assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
  destruct (nonce_forward_one e le1 m1 bl bi edge (rc + 1) eq_refl eq_refl
    ltac:(lia) ltac:(lia) HF1 PW1) as (m2 & HForward & HF2 & E2).
  replace (rc + 1 + 1) with (rc + 2) in HF2 by lia.
  assert (HI2 : frame_input_cells_at m2 bi edge (rc + 2) (encode h)).
  { eapply nonce_effects_input; [exact E2|cbn; intuition|].
    replace (rc + 2) with (rc + 1 + 1) by lia.
    exact (nonce_cells_tail m1 bi edge (rc + 1) None (encode h) HI1). }
  assert (HC2 : ctx_abs m2 bx bm l regs c ovf).
  { eapply (nonce_effects_ctx m1 m2 [bl] bx bm l regs c ovf); [exact E2| | | | |exact HC1]; cbn [List.In]; intuition congruence. }
  destruct (nonce_add_byte Hmodel e le1 m2 bx bm l regs c ovf (nonce_byte 1) 1
    eq_refl eq_refl Hmx Hgx Hgm Hcx Hcm (proj1 (proj2 nonce_prefix_ints)) HC2)
    as (mf & HAdd & HCtx & E3).
  exists mf. split.
  - unfold tagged_prefix. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1).
    + exact HRead.
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * apply eval_Etempvar. unfold le1. apply PTree.gss.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le1); eassumption.
  - split.
    + eapply nonce_effects_fields; [exact E3|cbn; intuition congruence|exact HF2].
    + split.
      * eapply nonce_effects_input; [exact E3|cbn; intuition congruence|exact HI2].
      * split; [exact HCtx|].
        eapply nonce_effects_union with (m1 := m2) (bs := [bl]) (cs := [bx; bm]);
          [eapply nonce_effects_trans; [exact E1|exact E2]|exact E3].
Qed.

Theorem tagged_confidential_prefix le m edge rc (odd : bool) (h : Ty.tySem Word256) l regs c ovf :
  0 <= rc -> rc + 258 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  frame_input_cells_at m bi edge rc
    (@encode nonce_conf_type (inl ((if odd then inr tt else inl tt), h))) ->
  ctx_abs m bx bm l regs c ovf ->
  let x := nonce_byte (if odd then z1 else z0) in
  exists mf,
    Clight2.exec_stmt elements_ge e le m (tagged_prefix itag iparity z0 z1) E0
      (PTree.set iparity (Vint (bit_int odd)) (PTree.set itag (Vint Int.zero) le)) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 2) /\
    frame_input_cells_at mf bi edge (rc + 2) (@encode Word256 h) /\
    ctx_abs mf bx bm (fst (absorb l regs [x])) (snd (absorb l regs [x]))
      (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1)) /\
    nonce_effects m mf [bl; bx; bm].
Proof.
  intros H0 HM HF PW HI HC x.
  assert (HI' : frame_input_cells_at m bi edge rc (Some false :: Some odd :: encode h)).
  { destruct odd; exact HI. }
  destruct (nonce_read_cell bl bm bb bx bi Hlx Hlm Hlg Hlc Hil le m edge rc false (Some odd :: encode h) l regs c ovf itag
    ltac:(lia) HF PW HI' HC) as (m1 & HRead1 & HF1 & HI1 & HC1 & E1).
  set (le1 := PTree.set itag (Vint Int.zero) le).
  assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
  destruct (nonce_read_cell bl bm bb bx bi Hlx Hlm Hlg Hlc Hil le1 m1 edge (rc + 1) odd (encode h) l regs c ovf iparity
    ltac:(lia) HF1 PW1 HI1 HC1) as (m2 & HRead2 & HF2 & HI2 & HC2 & E2).
  replace (rc + 1 + 1) with (rc + 2) in HF2, HI2 by lia.
  set (le2 := PTree.set iparity (Vint (bit_int odd)) le1).
  assert (HX : word8_array_value x = Int.repr (if odd then z1 else z0)).
  { unfold x. destruct odd; assumption. }
  destruct (nonce_add_byte Hmodel e le2 m2 bx bm l regs c ovf x (if odd then z1 else z0)
    eq_refl eq_refl Hmx Hgx Hgm Hcx Hcm HX HC2) as (mf & HAdd & HCtx & E3).
  exists mf. split.
  - unfold tagged_prefix. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1).
    + exact HRead1.
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * apply eval_Etempvar. unfold le1. apply PTree.gss.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le2).
        -- exact HRead2.
        -- eapply exec_Sifthenelse with (v1 := Vint (bit_int odd)) (b := odd).
           ++ apply eval_Etempvar. unfold le2. apply PTree.gss.
           ++ apply nonce_bit_bool.
           ++ destruct odd; exact HAdd.
  - split.
    + eapply nonce_effects_fields; [exact E3|cbn; intuition congruence|exact HF2].
    + split.
      * eapply nonce_effects_input; [exact E3|cbn; intuition congruence|exact HI2].
      * split; [exact HCtx|].
        eapply nonce_effects_union with (m1 := m2) (bs := [bl]) (cs := [bx; bm]);
          [eapply nonce_effects_trans; [exact E1|exact E2]|exact E3].
Qed.
End TaggedPrefix.
