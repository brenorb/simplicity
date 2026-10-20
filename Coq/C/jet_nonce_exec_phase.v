(** Complete nonce-processing phase between the real context reader/writer.
    The enclosing jet's entry, context parsing and final write/free are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_readBit_layout C.jet_read8s_layout C.jet_buffer_input.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_sha_ctx8_model C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_context_spec C.jet_nonce_context_shape.
Require Import C.jet_nonce_exec_effects C.jet_nonce_exec_calls C.jet_nonce_exec_prefix C.jet_nonce_exec_payload.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition nonce_present_temps (p : Ty.tySem nonce_conf_type) (le : temp_env) :=
  match p with
  | inr _ => PTree.set _t'3 (Vint Int.one) le
  | inl (odd, _) => PTree.set _t'2 (Vint (bit_int (match odd with inl _ => false | inr _ => true end)))
                     (PTree.set _t'3 (Vint Int.zero) le)
  end.
Definition nonce_phase_temps (a : Ty.tySem nonce_value_type) (le : temp_env) :=
  match a with
  | inl _ => PTree.set _t'4 (Vint Int.zero) le
  | inr p => nonce_present_temps p (PTree.set _t'4 (Vint Int.one) le)
  end.
Definition nonce_phase_count (a : Ty.tySem nonce_value_type) : Z :=
  match a with inl _ => 1 | inr _ => 33 end.
Definition nonce_phase_read_bits (a : Ty.tySem nonce_value_type) : Z :=
  match a with inl _ => 1 | inr _ => 259 end.
Definition nonce_phase_overflow (ovf : bool) (c : int64) (a : Ty.tySem nonce_value_type) :=
  match a with
  | inl _ => uc_overflow ovf c (Int64.repr 1)
  | inr _ => uc_overflow (uc_overflow ovf c (Int64.repr 1))
               (Int64.add c (Int64.repr 1)) (Int64.repr 32)
  end.

Lemma nonce_counter_one_then_32 c :
  Int64.add (Int64.add c (Int64.repr 1)) (Int64.repr 32) = Int64.add c (Int64.repr 33).
Proof. rewrite Int64.add_assoc. reflexivity. Qed.

Section Phase.
Variable Hmodel : memcpy_model.
Variables bl bm bb bx bi : block.
Hypotheses (Hlx : bl <> bx) (Hlm : bl <> bm) (Hlg : bl <> GC) (Hlc : bl <> GM).
Hypotheses (Hbx : bb <> bx) (Hbm : bb <> bm) (Hbg : bb <> GC) (Hbc : bb <> GM) (Hlb : bl <> bb).
Hypotheses (Hil : bi <> bl) (Hib : bi <> bb) (Hix : bi <> bx) (Him : bi <> bm).
Hypotheses (Hmx : bm <> bx) (Hgx : GC <> bx) (Hgm : GC <> bm) (Hcx : GM <> bx) (Hcm : GM <> bm).
Let e := nc_env bl bm bb bx.

Lemma nonce_present_prefix le m edge rc (p : Ty.tySem nonce_conf_type) l regs c ovf :
  0 <= rc -> rc + 258 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  frame_input_cells_at m bi edge rc (@encode nonce_conf_type p) -> ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m nc_prefix E0 (nonce_present_temps p le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 2) /\
    frame_input_cells_at mf bi edge (rc + 2) (encode (snd (nonce_prefix_value p))) /\
    ctx_abs mf bx bm (fst (absorb l regs [fst (nonce_prefix_value p)]))
      (snd (absorb l regs [fst (nonce_prefix_value p)]))
      (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1)) /\
    nonce_effects m mf [bl; bx; bm].
Proof.
  intros H0 HM HF PW HI HC. destruct p as [[[[]|[]] h]|h].
  - exact (nonce_confidential_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      le m edge rc false h l regs c ovf H0 HM HF PW HI HC).
  - exact (nonce_confidential_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      le m edge rc true h l regs c ovf H0 HM HF PW HI HC).
  - exact (nonce_explicit_prefix Hmodel bl bm bb bx bi Hlx Hlm Hlg Hlc Hil Hix Him Hmx Hgx Hgm Hcx Hcm
      le m edge rc h l regs c ovf H0 HM HF PW HI HC).
Qed.

Theorem nonce_phase_exec le m edge rc (a : Ty.tySem nonce_value_type) l regs c ovf :
  0 <= rc -> rc + 259 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 32 Cur Writable ->
  frame_input_cells_at m bi edge rc (@encode nonce_value_type a) -> ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m nc_nonce E0 (nonce_phase_temps a le) mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + nonce_phase_read_bits a) /\
    ctx_abs mf bx bm (fst (absorb l regs (nonce_hash_bytes a))) (snd (absorb l regs (nonce_hash_bytes a)))
      (Int64.add c (Int64.repr (nonce_phase_count a))) (nonce_phase_overflow ovf c a) /\
    nonce_effects m mf [bl; bb; bx; bm].
Proof.
  intros H0 HM HF PW PB HI HC. destruct a as [[]|p].
  - change (frame_input_cells_at m bi edge rc (Some false :: repeat None 258)) in HI.
    destruct (nonce_read_cell bl bm bb bx bi Hlx Hlm Hlg Hlc Hil le m edge rc false (repeat None 258)
      l regs c ovf _t'4 ltac:(lia) HF PW HI HC) as (m1 & HRead & HF1 & HI1 & HC1 & E1).
    set (le1 := PTree.set _t'4 (Vint Int.zero) le).
    destruct (nonce_add_byte Hmodel e le1 m1 bx bm l regs c ovf (nonce_byte 0) 0
      eq_refl eq_refl Hmx Hgx Hgm Hcx Hcm (proj1 nonce_prefix_ints) HC1)
      as (mf & HAdd & HCtx & E2).
    exists mf. split.
    + unfold nc_nonce. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1).
      * exact HRead.
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
        -- apply eval_Etempvar. unfold le1. apply PTree.gss.
        -- reflexivity.
        -- exact HAdd.
    + split.
      * eapply nonce_effects_fields; [exact E2|cbn; intuition congruence|exact HF1].
      * split; [exact HCtx|].
        eapply nonce_effects_mono with (bs := [bl; bx; bm]).
        -- eapply nonce_effects_union with (m1 := m1) (bs := [bl]) (cs := [bx; bm]); eassumption.
        -- intros b H. clear -H. cbn in H |- *. tauto.
  - change (frame_input_cells_at m bi edge rc (Some true :: @encode nonce_conf_type p)) in HI.
    destruct (nonce_read_cell bl bm bb bx bi Hlx Hlm Hlg Hlc Hil le m edge rc true (encode p)
      l regs c ovf _t'4 ltac:(lia) HF PW HI HC) as (m1 & HRead & HF1 & HI1 & HC1 & E1).
    set (le1 := PTree.set _t'4 (Vint Int.one) le).
    assert (PW1 : Mem.valid_access m1 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
    destruct (nonce_present_prefix le1 m1 edge (rc + 1) p l regs c ovf
      ltac:(lia) ltac:(lia) HF1 PW1 HI1 HC1) as (m2 & HPrefix & HF2 & HI2 & HC2 & E2).
    replace (rc + 1 + 2) with (rc + 3) in HF2, HI2 by lia.
    set (le2 := nonce_present_temps p le1).
    assert (PW2 : Mem.valid_access m2 Mint64 bl 8 Writable) by (eapply nonce_effects_access; eassumption).
    assert (PB2 : Mem.range_perm m2 bb 0 32 Cur Writable).
    { intros ofs HO. apply (nonce_perms _ _ _ E2), (nonce_perms _ _ _ E1), PB, HO. }
    destruct (nonce_payload_exec Hmodel le2 m2 bl bm bb bx bi edge (rc + 3) (snd (nonce_prefix_value p))
      (fst (absorb l regs [fst (nonce_prefix_value p)]))
      (snd (absorb l regs [fst (nonce_prefix_value p)]))
      (Int64.add c (Int64.repr 1)) (uc_overflow ovf c (Int64.repr 1))
      Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb ltac:(congruence) ltac:(congruence)
      Hmx Hgx Hgm Hcx Hcm ltac:(lia) ltac:(lia) HF2 PW2 PB2 HI2 HC2)
      as (mf & HPayload & HFields & HCtx & E3).
    replace (rc + 3 + 256) with (rc + 259) in HFields by lia.
    rewrite absorb_app, nonce_counter_one_then_32 in HCtx.
    exists mf. split.
    + unfold nc_nonce. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1).
      * exact HRead.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- apply eval_Etempvar. unfold le1. apply PTree.gss.
        -- reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le2); eassumption.
    + split; [exact HFields|]. split; [exact HCtx|].
      eapply nonce_effects_trans; [|exact E3].
      eapply nonce_effects_trans.
      * eapply nonce_effects_mono; [exact E1|]. intros b H. clear -H. cbn in H |- *. tauto.
      * eapply nonce_effects_mono; [exact E2|]. intros b H. clear -H. cbn in H |- *. tauto.
Qed.
End Phase.
