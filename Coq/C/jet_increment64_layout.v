(** End-to-end increment_64 equivalence for arbitrary non-wrapping layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_frame_layout.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_carry_wide_layout C.jet_wide.
Require Import C.jet_output_slice C.jet_read64_input_word_total.
Require Import C.jet_read64_input_word.
Require Import C.jet_increment64_wide_word C.jet_increment64_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_increment64_layout_matches_spec m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem (Word 6)) cursor read_cursor :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 64 ->
  frame_input_word_at m bi edge read_cursor x ->
  write_frame_at m bd dbase bw outedge cursor 65 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_increment_64)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vundef]
      E0 mf (Vint Int.one) /\
    carry_wide_output_at W64 mf bw outedge cursor
      (@increment64_spec Alg.CoreFunSem x) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 65) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= slice_write_low 64 outedge (cursor - 1) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSourceBase HSourceAlign [HSourceEdge HSourceCursor]
      HReadCursor HInput HOutput.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof HOutput as [HDBase [[HDE HDO] [HOutEdge [HN [HMax [HDw [PD HW]]]]]]].
  pose proof (HW 0 ltac:(lia)) as HW0.
  cbn zeta in HW0. destruct HW0 as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs).
  { eapply fresh_frame_not_loaded; eauto. }
  assert (HLi : bl <> bi).
  { pose proof (frame_input_word_at_bit64 m bi edge read_cursor x 0
      HInput ltac:(lia)) as Hbit.
    destruct Hbit as [_ [_ [w [HL _]]]]. eapply fresh_frame_not_loaded; eauto. }
  assert (HLd : bl <> bd).
  { eapply fresh_frame_not_loaded; eauto. }
  assert (HLw : bl <> bw).
  { eapply fresh_frame_not_loaded; eauto. }
  assert (HSEa : Mem.load Mptr ma bs sbase =
      Some (Vptr bi (Ptrofs.repr edge))).
  { eapply Mem.load_alloc_other; eauto. }
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) =
      Some (Vlong (Int64.repr read_cursor))).
  { eapply Mem.load_alloc_other; eauto. }
  destruct (frame_loadbytes_at ma bs sbase _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa)
    as [HLE HLO].
  assert (HInputC : frame_input_word_at mc bi edge read_cursor x).
  { eapply frame_input_bits_at_preserved; [|exact HInput].
    intros ofs w HL.
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    left. congruence. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|].
    exists 1; reflexivity. }
  destruct (eval_read64_word_at mc bl 0 bi edge read_cursor x HLocalBase
      HReadCursor (conj HLE HLO) HInputC PLC HLi)
    as [mr [r [Hread [Hr [HReadFields [HReadMem [HReadPerm HReadValid]]]]]]].
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
      Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v HBw HL.
    rewrite HReadMem by (left; destruct HBw; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct HBw; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p,
      Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutputR : write_frame_at mr bd dbase bw outedge cursor 65).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_carry_wide_layout W64 mr bd dbase bw outedge cursor
      (increment64_carry r) (increment64_payload r) HOutputR)
    as [mb [me [Hbit [Hwrite [Hvalue [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]]]].
  pose proof Hvalue as HvalueIncrementC.
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_increment64_layout_composes with
      (ma := ma) (mc := mc) (mr := mr) (mb := mb) (me := me)
      (bl := bl) (bytes := bytes) (r := r); eauto.
  - split.
    + eapply carry_wide_output_at_preserved.
      * intros ofs w HWide. erewrite Mem.load_free; [exact HWide|exact HF|auto].
      * cbn [wide_bits] in HvalueIncrementC.
        rewrite Int64.zero_ext_above in HvalueIncrementC
          by (assert (Hws : Int64.zwordsize = 64) by reflexivity; rewrite Hws; lia).
        rewrite (increment64_values_denote_input r x Hr) in HvalueIncrementC.
        exact HvalueIncrementC.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w Hload. eapply HBeforeLoad; eauto.
        -- intros ofs w Hload. erewrite Mem.load_free; [exact Hload|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmem by assumption.
           rewrite HReadMem by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|].
           ++ eapply Mem.load_alloc_unchanged; eauto.
           ++ left; exact Hbl.
Qed.
