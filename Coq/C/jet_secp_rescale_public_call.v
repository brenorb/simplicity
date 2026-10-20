(** Full original public function, from input frames to the literal result.
    All reader/helper/writer calls, allocations and frees are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy C.jet_secp_square_spec_bridge C.jet_secp_rescale_owned
  C.jet_secp_rescale_literal C.jet_secp_rescale_writer C.jet_secp_rescale_public_entry
  C.jet_secp_rescale_public_body C.jet_secp_rescale_public_prepare C.jet_secp_rescale_public_reads.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_rescale Simplicity.Translate.encode.

Theorem eval_gej_rescale_literal_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y z s : tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 768 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits s)) ->
  0 <= rc -> rc+1024 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_rescale)
      [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_rescale Alg.CoreFunSem (((x,y),z),s))) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HN HBase HAlign HSource HX HY HZ HS Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 128) as [mb bp] eqn:HB.
  destruct (Mem.alloc mb 0 40) as [mc bc] eqn:HC.
  destruct (rescale_allocations_fresh m0 ma mb mc bl bp bc HA HB HC)
    as (HNewL & HNewP & HNewC & HPL & HCL & HPC).
  set (le := secp_public_temps v_env bd dbase bs sbase).
  destruct (rescale_prepare_public le m0 ma mb mc bl bp bc bd dbase bs sbase bw outedge cursor N bi edge rc
    HA HB HC ltac:(unfold le,secp_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    HO HBase HAlign HSource) as (md & CCopy & FPD & FCD & FLD & SrcD & HSep & FinD & FrameD).
  destruct (eval_rescale_public_reads m0 bd dbase bw outedge cursor N bi edge rc x y z s md bp bc bl
    HO HN HX HY HZ HS Hrc HM FPD FCD FLD SrcD HPL HCL HPC HSep FinD)
    as (mr & ms & CPoint & CScale & X & Y & Z & S & Flag & FPS & FCS & FLS & FinS & FrameS).
  destruct (eval_gej_rescale_owned (square_reader_rho x) (square_reader_rho y) (square_reader_rho z)
    (square_reader_rho s) ms bp bc _ (square_reader_bounds x) (square_reader_bounds y)
    (square_reader_bounds z) (square_reader_bounds s) HPC X Y Z S FPS FCS Flag)
    as (mn & CHelper & XN & YN & ZN & SN & FlagN & FPN & FCN & BX & BY & BZ & FrameN).
  assert (HExtN : eqext m0 bd bw bi ms mn).
  { eapply lframe_implies; [exact FrameN|].
    intros b pos HE HV; split; intro HB'; subst b;
      [exact (HSep 0%nat ltac:(cbn;lia) HE)|exact (HSep 1%nat ltac:(cbn;lia) HE)]. }
  assert (FinN : finv m0 bd dbase bw outedge cursor N bi mn false []).
  { eapply finv_stable; [exact HO|exact FinS|exact HExtN]. }
  assert (HVL : Mem.valid_block ms bl) by (eapply Mem.perm_valid_block; apply (FLS 0);lia).
  assert (FLN : Mem.range_perm mn bl 0 16 Cur Freeable).
  { intros pos HP; apply (proj1 (proj2 FrameN)); [exact HVL|split;congruence|apply FLS;exact HP]. }
  assert (HSPoint : xsep (extA m0 bd bw bi) [(bp,0)]).
  { intros [|r] HI; [exact (HSep 0%nat ltac:(cbn;lia))|cbn in HI;lia]. }
  destruct (eval_write_gej_rescaled_literal m0 bd dbase bw outedge cursor N bi rc mn bp x y z s
    HO HN FinN XN YN ZN FPN HSPoint) as (mw & CWrite & FinW & FPW & FrameW).
  assert (HVLC : Mem.valid_block mn bl) by (eapply Mem.perm_valid_block; apply (FLN 0);lia).
  assert (HVCC : Mem.valid_block mn bc) by (eapply Mem.perm_valid_block; apply (FCN 0);lia).
  assert (FLW : Mem.range_perm mw bl 0 16 Cur Freeable).
  { intros pos HP; apply (proj1 (proj2 FrameW)); [exact HVLC|split;[congruence|exact (HSep 2%nat ltac:(cbn;lia))]|apply FLN;exact HP]. }
  assert (FCW : Mem.range_perm mw bc 0 40 Cur Freeable).
  { intros pos HP; apply (proj1 (proj2 FrameW)); [exact HVCC|split;[congruence|exact (HSep 1%nat ltac:(cbn;lia))]|apply FCN;exact HP]. }
  destruct (rescale_free_public_locals mw bl bp bc HPL HCL HPC FLW FPW FCW) as (mf & HFree & FrameF).
  assert (HExtF : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact FrameF|].
    intros b pos [_ HV] _; repeat split; intro HE; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := rescale_public_env bl bp bc) (le1 := le) (le2 := le)
      (m1 := mc) (m2 := mw) (out := Out_return (Some (Vint Int.one,tint))).
    + eapply rescale_public_entry; eassumption.
    + rewrite rescale_public_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := md) (le1 := le).
      * exact CCopy.
      * eapply exec_rescale_public_rest; [|exact CPoint|exact CScale|exact CHelper|exact CWrite].
        unfold le,secp_public_temps; rewrite !PTree.gso by discriminate; apply PTree.gss.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split; [eapply finv_stable; [exact HO|exact FinW|exact HExtF]|].
    assert (HF : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
    { eapply lframe_trans.
      - eapply lframe_implies; [exact FrameD|].
        intros b pos [HV HE] _; repeat split; intro HB'; subst b; contradiction.
      - eapply lframe_trans.
        + eapply lframe_implies; [exact FrameS|].
          intros b pos [HV HE] _; unfold rescale_locals_outside.
          repeat split; try exact HE; intro HB'; subst b; contradiction.
        + eapply lframe_trans.
          * eapply lframe_implies; [exact FrameN|].
            intros b pos [HV HE] _; split; intro HB'; subst b; contradiction.
          * eapply lframe_trans.
            -- eapply lframe_implies; [exact FrameW|].
               intros b pos [HV HE] _; split; [intro HB';subst b;contradiction|exact HE].
            -- eapply lframe_implies; [exact FrameF|].
               intros b pos [HV HE] _; repeat split; intro HB'; subst b; contradiction. }
    eapply lframe_implies; [exact HF|]; intros b pos HE HV; split; assumption.
Qed.
