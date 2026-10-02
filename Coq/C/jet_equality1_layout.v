(** Complete eq_1 call against Generic.eq, from initial-only frame contracts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_equality_spec C.jet_equality1_exec.
Require Import C.jet_readBit_layout C.jet_writeBit_layout_total.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_eq1_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (x y : Ty.tySem (Word 0)) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 2 ->
  frame_input_bit_at m bi edge rc (Bit.toBool x) ->
  frame_input_bit_at m bi edge (rc + 1) (Bit.toBool y) ->
  write_frame_at m bd dbase bw outedge cursor 1 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_eq_1)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@equality_spec (Word 0) Alg.CoreFunSem (x, y))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 1) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 1) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput1 Hinput2 Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 1 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput1 as [_ [_ [w [HL _]]]]. eapply fresh_frame_not_loaded; eauto. }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_loadbytes_at ma bs sbase _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa) as [HLE HLO].
  assert (HInputC1 : frame_input_bit_at mc bi edge rc (Bit.toBool x)).
  { eapply frame_input_bit_at_preserved; [|exact Hinput1].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC1 : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_readBit_layout mc bl 0 bi edge rc (Bit.toBool x) HLocalBase ltac:(lia)
    (conj HLE HLO) HInputC1 PLC1)
    as (mr & Hread1 & HReadFields1 & HReadMem1 & HReadPerm1 & HReadValid1).
  assert (HInputR2 : frame_input_bit_at mr bi edge (rc + 1) (Bit.toBool y)).
  { eapply frame_input_bit_at_preserved; [|exact Hinput2].
    intros ofs w HL. rewrite HReadMem1 by (left; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC2 : Mem.valid_access mr Mint64 bl 8 Writable).
  { destruct PLC1 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm1. apply HP; exact Hrange. }
  destruct (eval_readBit_layout mr bl 0 bi edge (rc + 1) (Bit.toBool y) HLocalBase ltac:(lia)
    HReadFields1 HInputR2 PLC2)
    as (mr2 & Hread2 & HReadFields2 & HReadMem2 & HReadPerm2 & HReadValid2).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr2 b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    rewrite HReadMem2 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem1 by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr2 b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr2 bd dbase bw outedge cursor 1).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_writeBit_layout mr2 bd dbase bw outedge cursor
    (eq1_bit (Bit.toBool x) (Bit.toBool y)) HOutR)
    as (me & w & Hwrite & Hload & Hbit & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_eq1_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply carry_output_encode; [lia|]. exists w. split; [exact Hload|].
        rewrite Hbit. destruct x as [[]|[]], y as [[]|[]]; reflexivity.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w' HL. eapply HBeforeLoad; eauto.
        -- intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption. rewrite HReadMem2 by (left; exact Hbl).
           rewrite HReadMem1 by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem eq1_local_spec : jet_local_spec f_simplicity_eq_1 (Ty.Prod (Word 0) (Word 0)) Bit
  (fun xy => @equality_spec (Word 0) Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Bit)) with 1 in Hout.
  change (Z.of_nat (bitSize (Ty.Prod (Word 0) (Word 0)))) with 2 in Hmax.
  eapply eval_eq1_layout_matches_spec; eauto; [lia| |].
  - specialize (Hin 0%nat (Some (Bit.toBool x)) ltac:(destruct x as [[]|[]], y as [[]|[]]; reflexivity)).
    change (frame_input_bit_at m bi edge (rc + 0) (Bit.toBool x)) in Hin.
    rewrite Z.add_0_r in Hin. exact Hin.
  - specialize (Hin 1%nat (Some (Bit.toBool y)) ltac:(destruct x as [[]|[]], y as [[]|[]]; reflexivity)).
    exact Hin.
Qed.
Theorem eq1_context : jet_context_for f_simplicity_eq_1 (@equality_spec (Word 0)).
Proof.
  exact (jet_context _ _ (equality_spec_parametric (Word 0)) eq1_local_spec ltac:(vm_compute; lia)).
Qed.
Definition eq1_guarantees := jet_local_spec_guarantees _ _ _ _ eq1_local_spec.
Definition eq1_context_guarantees :=
  jet_context_guarantees _ _ (equality_spec_parametric (Word 0)) eq1_local_spec ltac:(vm_compute; lia).

