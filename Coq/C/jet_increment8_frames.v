(** Full increment equivalence with arbitrary two-word input alignment and all output cursors 9..72. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_read8_position.
Require Import C.jet_increment8 C.jet_increment8_exec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_increment8_spec C.jet_increment8_word C.jet_input_position C.jet_two_word_input C.jet_read8_two_words.
Require Import C.jet_crossing_frame C.jet_carry_byte_crossing C.jet_increment8_crossing_word C.jet_output9.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem eval_increment8_frames_matches_spec m bd bs bi bw (x : Ty.tySem Word8) cursor read_cursor :
  9 <= cursor <= 72 ->
  two_word_input m bs bi read_cursor [x] ->
  write_frame m bd bw 0 cursor 9 ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef] E0 mf (Vint Int.one) /\
    output9 mf bw cursor (@increment8_spec Alg.CoreFunSem x) /\
    output9_prefix m mf bw cursor /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (cursor - 9))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HK HInput HOutput.
  destruct (two_word_input_single m bs bi read_cursor x HInput)
    as [inputhigh [inputlow [[HSE HSO] [HRead [HIH [HIL Hdecode]]]]]].
  pose proof HOutput as [[HDE HDO] [HN [HMax [HDw [PD HW]]]]].
  pose proof (HW 0 ltac:(lia)) as HW0.
  cbn zeta in HW0. destruct HW0 as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs 0 = Some (Vptr bi (Ptrofs.repr 16)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs 8 = Some (Vlong (Int64.repr read_cursor)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_loadbytes ma bs _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange | constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields ma mc bs bl bytes _ _ HB SC HSEa HSOa)
    as [HLE HLO].
  assert (HIHC : Mem.load Mint64 mc bi 8 = Some (Vlong inputhigh)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HILC : Mem.load Mint64 mc bi 0 = Some (Vlong inputlow)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA | lia | cbn; lia |].
    exists 1; reflexivity. }
  destruct (eval_read8_two_words mc bl bi read_cursor inputhigh inputlow HRead
    (conj HLE HLO) HIHC HILC PLC HLi)
    as [mr [Hread [HReadFields [HReadMem [HReadPerm HReadValid]]]]].
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v HBw HL.
    
    rewrite HReadMem by (destruct HBw; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct HBw; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP.  apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutputR : write_frame mr bd bw 0 cursor 9).
  { eapply write_frame_preserved; eauto. }
  set (r := read8_result (two_word_byte read_cursor inputhigh inputlow)).
  set (carry := Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  destruct (eval_carry_byte_output9 mr bd bw cursor carry (increment8_byte r) HK HOutputR)
    as [mb [me [Hbit [Hwrite [Hvalue [Hprefix [Hoff [Hmem Hperm]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm.
    apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC |]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply ClightBigstep.eval_funcall_internal
      with (e := e_increment8 bl) (le1 := le_increment8 bd bs Ptrofs.zero)
        (m1 := ma) (le2 := le_increment8_x bd bs Ptrofs.zero r)
        (m2 := me) (out := Out_return (Some (Vint Int.one, tint)))
        (vres := Vint Int.one).
    + apply entry_increment8; exact HA.
    + eapply increment8_body_composes.
      * eapply exec_increment8_copy with (bytes := bytes).
        -- reflexivity.
        -- intros _. exists 0; reflexivity.
        -- intros _. exists 0; reflexivity.
        -- left; exact HLs.
        -- exact HB.
        -- exact SC.
      * eapply call_increment8_read.
        -- apply symbol_read8.
        -- apply funct_read8.
        -- exact Hread.
      * eapply call_increment8_writeBit with (bit := increment8_carry_bit r)
          (vret := Vint (increment8_carry_bit r)).
        -- reflexivity.
        -- apply eval_increment8_carry.
        -- apply cast_increment8_carry.
        -- apply symbol_writeBit.
        -- apply funct_writeBit.
        -- exact Hbit.
      * eapply call_increment8_write with (x := increment8_byte r).
        -- reflexivity.
        -- apply eval_increment8_sum.
        -- apply cast_increment8_sum.
        -- apply symbol_write8.
        -- apply funct_write8.
        -- exact Hwrite.
    + cbn; split; [discriminate | reflexivity].
    + change (Mem.free_list me [(bl, 0, 16)] = Some mf).
      cbn. rewrite HF. reflexivity.
  - split.
    + eapply output9_preserved.
      * intros ofs w HWf. erewrite Mem.load_free; [exact HWf|exact HF|auto].
      * unfold carry, r in Hvalue.
        rewrite increment8_carry_byte_spec, Hdecode in Hvalue.
        exact Hvalue.
    + split.
      * eapply output9_prefix_preserved; [| |exact Hprefix].
        -- intros ofs w HWm. eapply HBeforeLoad; eauto.
        -- intros ofs w HWf. erewrite Mem.load_free; [exact HWf|exact HF|auto].
      * split.
        -- erewrite Mem.load_free; [exact Hoff|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmem; [|apply HReadValid; eauto using Mem.storebytes_valid_block_1,
             Mem.valid_block_alloc|exact Hbd|exact Hbw].
           rewrite HReadMem by exact Hbl.
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.



