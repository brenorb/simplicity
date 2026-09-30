(** Full increment C-to-Simplicity equivalence with arbitrary non-wrapping input/output layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_read8_position.
Require Import C.jet_increment8 C.jet_increment8_exec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_increment8_spec C.jet_increment8_word C.jet_input_position C.jet_two_word_input C.jet_read8_two_words.
Require Import C.jet_crossing_frame C.jet_carry_byte_crossing C.jet_increment8_crossing_word C.jet_output9.
Require Import C.jet_input_layout C.jet_frame_layout C.jet_frame_copy_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_carry_byte_layout C.jet_increment8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem eval_increment8_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge (x : Ty.tySem Word8) cursor read_cursor :
  byte_input_at m bs sbase bi edge read_cursor [x] ->
  write_frame_at m bd dbase bw outedge cursor 9 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_increment_8)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    carry_byte_output_at mf bw outedge cursor (@increment8_spec Alg.CoreFunSem x) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 9) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= byte_write_low outedge (cursor - 1) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HInput HOutput.
  destruct (byte_input_single_at m bs sbase bi edge read_cursor x HInput)
    as [HBase [[HSE HSO] HX]].
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof HOutput as [HDBase [[HDE HDO] [HOutEdge [HN [HMax [HDw [PD HW]]]]]]].
  pose proof (HW 0 ltac:(lia)) as HW0.
  cbn zeta in HW0. destruct HW0 as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct HX as [_ [_ [h [l [HH _]]]]]. eapply fresh_frame_not_loaded; eauto. }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr read_cursor)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_loadbytes_at ma bs sbase _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange | constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa)
    as [HLE HLO].
  assert (HXC : byte_slice_at mc bi edge read_cursor x).
  { eapply byte_slice_preserved; [|exact HX].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA | lia | cbn; lia |].
    exists 1; reflexivity. }
  destruct (eval_read8_byte_at mc bl 0 bi edge read_cursor x HLocalBase
    (conj HLE HLO) HXC PLC HLi)
    as [mr [payload [Hread [Hdecode [HReadFields [HReadMem [HReadPerm HReadValid]]]]]]].
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v HBw HL.

    rewrite HReadMem by (left; destruct HBw; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct HBw; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP.  apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutputR : write_frame_at mr bd dbase bw outedge cursor 9).
  { eapply write_frame_at_preserved; eauto. }
  set (r := read8_result payload).
  set (carry := Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  destruct (eval_carry_byte_layout mr bd dbase bw outedge cursor carry (increment8_byte r) HOutputR)
    as [mb [me [Hbit [Hwrite [Hvalue [Hprefix [Hoff [Hmem [Hperm Hvalid]]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm.
    apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC |]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_increment8_layout_composes with (ma := ma) (mc := mc) (mr := mr)
      (mb := mb) (me := me) (bl := bl) (bytes := bytes) (r := r); eauto.
    exact (proj2 (Mem.load_valid_access _ _ _ _ _ HSE)).
  - split.
    + eapply carry_byte_output_at_preserved.
      * intros ofs w HWf. erewrite Mem.load_free; [exact HWf|exact HF|auto].
      * unfold carry, r in Hvalue.
        rewrite increment8_carry_byte_spec, Hdecode in Hvalue.
        exact Hvalue.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HWm. eapply HBeforeLoad; eauto.
        -- intros ofs w HWf. erewrite Mem.load_free; [exact HWf|exact HF|auto].
      * split.
        -- destruct Hoff as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmem by assumption.
           rewrite HReadMem by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.
