(** Four actual C calls from the full input pair to the original writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory AST Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_encoding C.jet_frame_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_writer_bridge C.jet_secp_multiply_writer_call.
Require Import C.jet_secp_multiply_input_input C.jet_secp_multiply_input_reader C.jet_secp_multiply_input_pair.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma two_field_foot_owner ba bb b pos :
  foot [(ba, 0); (bb, 0)] (map rshape field_mul_regs) b pos -> b = ba \/ b = bb.
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]]; [left; exact HB|right; exact HB|destruct r; discriminate].
Qed.
Lemma frame_fields_on_unchanged_block m mf bl bi edge rc : Mem.valid_block m bl ->
  frame_fields_at m bl 0 bi edge rc -> lframe (fun b _ => b = bl) m mf ->
  frame_fields_at mf bl 0 bi edge rc.
Proof.
  intros HV [HP HC] [HL _]; split.
  - rewrite HL; [exact HP|exact HV|intros; reflexivity].
  - rewrite HL; [exact HC|exact HV|intros; reflexivity].
Qed.

Local Opaque secp_ge pair_rho normalized_value input_product_word Simplicity.Translate.encode.
Theorem eval_original_read_pair_mul_write m0 bd dbase bw outedge cursor N bi edge rc
    (x y : Ty.tySem (Word 8)) m ba bb bl :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_input_cells_at m0 bi edge rc
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (x, y)) ->
  0 <= rc -> rc + 512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  ba <> bb -> ba <> bl -> bb <> bl ->
  xsep (extA m0 bd bw bi) [(ba, 0); (bb, 0); (bl, 0)] ->
  finv m0 bd dbase bw outedge cursor N bi m false [] ->
  exists ma mr mm mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef /\
    Clight2.eval_funcall secp_ge ma (Internal f_read_fe)
      [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mr Vundef /\
    Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_mul)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mm Vundef /\
    Clight2.eval_funcall secp_ge mm (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (@Simplicity.Translate.encode (Word 8) (input_product_word x y)) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\ frame_fields_at mf bl 0 bi edge (rc + 512) /\
    lframe (pair_locals_outside (extA m0 bd bw bi) ba bb bl) m mf.
Proof.
  intros HO HC HInput HCursor HMax HFA HFB HFL HFields HDAB HDAL HDBL HS HI.
  destruct (eval_read_field_pair m0 bd dbase bw outedge cursor N bi edge rc x y
    m ba bb bl HO HC HInput HCursor HMax HFA HFB HFL HFields HDAB HDAL HDBL HS HI)
    as (ma & mr & HRA & HRB & HFieldA & HFieldB & HFreeA & HFreeB & HFreeL & HNext & HInv & HReadFrame).
  pose proof (pair_initial_rep x y mr ba bb HFieldA HFieldB HFreeA HFreeB HDAB) as HR.
  assert (HSW : xsep (extA m0 bd bw bi) [(ba, 0); (bb, 0)]).
  { intros r Hr; destruct r as [|[|r]].
    - exact (HS 0%nat ltac:(cbn; lia)).
    - exact (HS 1%nat ltac:(cbn; lia)).
    - cbn in Hr; lia. }
  assert (HWI : invA m0 bd dbase bw outedge cursor N bi (rc + 512) false [] 256
    (cursor_rho (rc + 512)) [] mr).
  { change (Int64.repr (rc + 512) = Int64.repr (rc + 512) /\
      finv m0 bd dbase bw outedge cursor N bi mr false [] /\ 256 <= N /\ 0 <= 256).
    split; [reflexivity|]; split; [exact HInv|]; split; [exact HC|lia]. }
  destruct (eval_original_field_mul_then_write m0 bd dbase bw outedge cursor N bi
    (rc + 512) false [] (pair_rho x y) [(ba, 0); (bb, 0)] mr
    HO (pair_input_bounds x y) HR HSW HWI)
    as (mm & mf & HM & HW & HFinal & HSecond & HFreeAFinal & HFreeBFinal & HWriteFrame).
  rewrite pair_product_word in HFinal; cbn [app] in HFinal.
  assert (HVL : Mem.valid_block mr bl) by (eapply Mem.perm_valid_block; apply (HFreeL 0); lia).
  assert (HOtherL : lframe (fun b _ => b = bl) mr mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros b pos -> HValid; split; [exact HVL|]; split.
    - intro HFoot; apply two_field_foot_owner in HFoot; destruct HFoot; congruence.
    - exact (HS 2%nat ltac:(cbn; lia)). }
  assert (HFreeLFinal : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HP; eapply (proj1 (proj2 HOtherL)); [exact HVL|reflexivity|apply HFreeL; exact HP]. }
  pose proof (frame_fields_on_unchanged_block mr mf bl bi edge (rc + 512) HVL HNext HOtherL) as HNextFinal.
  assert (HOutside : lframe (pair_locals_outside (extA m0 bd bw bi) ba bb bl) mr mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros b pos [HBA [HBB [HBL HE]]] HV; split; [exact HV|]; split; [|exact HE].
    intro HFoot; apply two_field_foot_owner in HFoot; destruct HFoot; contradiction. }
  exists ma, mr, mm, mf; split; [exact HRA|]; split; [exact HRB|]; split; [exact HM|];
    split; [exact HW|]; split; [exact HFinal|]; split; [exact HFreeAFinal|];
    split; [exact HFreeBFinal|]; split; [exact HFreeLFinal|]; split; [exact HNextFinal|].
  eapply lframe_trans; eassumption.
Qed.
