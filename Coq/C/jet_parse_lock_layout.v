(** Complete parse_lock C-to-canonical-Simplicity equivalence, including
    arbitrary valid input/output cursors and crossings. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate C.jets C.jet_exec C.jet_frame_layout.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_carry_wide_layout C.jet_wide.
Require Import C.jet_output_slice C.jet_read32_input_word C.jet_read32_input_word_total.
Require Import C.jet_increment32_wide_word C.jet_increment32_layout_exec.
Require Import C.jet_constant_layout C.jet_complement_wide_layout C.jet_timelock_spec C.jet_parse_lock_exec.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_parse_lock_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem (Word 5)) cursor read_cursor :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bi edge read_cursor x ->
  write_frame_at m bd dbase bw outedge cursor 33 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_parse_lock)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
      E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode
      (@parse_lock_spec Alg.CoreFunSem x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 33) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= slice_write_low 32 outedge (cursor - 1) \/
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
  { pose proof (frame_input_word_at_bit32 m bi edge read_cursor x 0
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
  destruct (eval_read_wide_word_at W32 mc bl 0 bi edge read_cursor x HLocalBase
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
  assert (HOutputR : write_frame_at mr bd dbase bw outedge cursor 33).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_carry_wide_layout W32 mr bd dbase bw outedge cursor
      (parse_lock_tag r) r HOutputR)
    as [mb [me [Hbit [Hwrite [Hvalue [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_parse_lock_composes with
      (ma := ma) (mc := mc) (mr := mr) (mb := mb) (me := me)
      (bl := bl) (bytes := bytes) (r := r); eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * rewrite <- (parse_lock_int64_denotes x r Hr), encode_equal_sum_word.
        apply (carry_wide_output_encode W32); [change (33 <= cursor); lia|exact Hvalue].
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

Theorem parse_lock_local_spec : jet_local_spec f_simplicity_parse_lock
  (Word 5) (Ty.Sum (Word 5) (Word 5)) (fun x => @parse_lock_spec Alg.CoreFunSem x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 5))) with 32 in Hmax.
  change (Z.of_nat (bitSize (Ty.Sum (Word 5) (Word 5)))) with 33 in *.
  apply frame_input_word_at_encode in Hin.
  destruct (eval_parse_lock_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    x cursor rc HB HA HF ltac:(lia) Hin Hout) as (mf & Hcall & Hobs & Hpre & Hfields & Hpres).
  exists mf. split; [exact Hcall|]. split; [exact Hobs|]. split; [exact Hpre|].
  split; [exact Hfields|]. eapply loads_weaken; [|exact Hpres].
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout).
  replace (cursor - 33) with (cursor - 1 - 32) by lia. apply slice_write_low_bound; lia.
Qed.

Theorem parse_lock_context : jet_context_for f_simplicity_parse_lock (@parse_lock_spec).
Proof.
  exact (jet_context _ _ parse_lock_spec_parametric parse_lock_local_spec ltac:(vm_compute; lia)).
Qed.
Definition parse_lock_guarantees := jet_local_spec_guarantees _ _ _ _ parse_lock_local_spec.
Definition parse_lock_context_guarantees :=
  jet_context_guarantees _ _ parse_lock_spec_parametric parse_lock_local_spec ltac:(vm_compute; lia).
