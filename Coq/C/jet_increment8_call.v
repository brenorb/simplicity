(** Total concrete-layout execution: only initial loads and write permissions
    are premises; every allocation, copy, helper call, store and free is proved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_one8 C.jet_read8 C.jet_increment8.
Require Import C.jet_increment8_exec C.jet_frame_copy C.jets.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Require Import C.jet_increment8_updates C.jet_increment8_general_exec.
Local Open Scope Z_scope.

Theorem eval_increment8_concrete_word m bd bs bi bw w old :
  Mem.load Mptr m bs 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bs 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong w) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  bd <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 =
      Some (Vlong (increment8_word_update old (read8_result w))) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
    (forall chunk b ofs, Mem.valid_block m b -> b <> bd -> b <> bw ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSE HSO HI HDE HDO HW PD PW HDw.
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs 0 = Some (Vptr bi (Ptrofs.repr 8)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs 8 = Some (Vlong (Int64.repr 56)))
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
  assert (HIC : Mem.load Mint64 mc bi 0 = Some (Vlong w)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HDEC : Mem.load Mptr mc bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HDOC : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr 9))).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HWC : Mem.load Mint64 mc bw 0 = Some (Vlong old)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (PDC : Mem.valid_access mc Mint64 bd 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  assert (PWC : Mem.valid_access mc Mint64 bw 0 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA | lia | cbn; lia |].
    exists 1; reflexivity. }
  destruct (Mem.valid_access_store mc Mint64 bl 8 (Vlong (Int64.repr 64)) PLC)
    as [mr SR].
  assert (PDR : Mem.valid_access mr Mint64 bd 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mr Mint64 bd 8 (Vlong (Int64.repr 8)) PDR)
    as [mo SO].
  assert (PWO : Mem.valid_access mo Mint64 bw 0 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mo Mint64 bw 0
    (Vlong (increment8_carry_update old (read8_result w))) PWO) as [mb SB].
  assert (PWB : Mem.valid_access mb Mint64 bw 0 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mb Mint64 bw 0
    (Vlong (increment8_word_update old (read8_result w))) PWB) as [mw SW].
  assert (PDW : Mem.valid_access mw Mint64 bd 8 Writable)
    by (eauto 8 using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong Int64.zero) PDW)
    as [me SE].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange.
    eapply Mem.perm_store_1; [exact SE |].
    eapply Mem.perm_store_1; [exact SW |].
    eapply Mem.perm_store_1; [exact SB |].
    eapply Mem.perm_store_1; [exact SO |].
    eapply Mem.perm_store_1; [exact SR |].
    eapply Mem.perm_storebytes_1; [exact SC |].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  destruct (increment8_helper_statements_word mc mr mo mb mw me bl bd bs bi bw w old
    HLE HLO HIC HDEC HDOC HWC HLd HLw HDw SR SO SB SW SE)
    as [Hread [Hbit Hwrite]].
  exists mf. split.
  - eapply ClightBigstep.eval_funcall_internal
      with (e := e_increment8 bl) (le1 := le_increment8 bd bs Ptrofs.zero)
        (m1 := ma) (le2 := le_increment8_x bd bs Ptrofs.zero (read8_result w))
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
      * exact Hread.
      * exact Hbit.
      * exact Hwrite.
    + cbn; split; [discriminate | reflexivity].
    + change (Mem.free_list me [(bl, 0, 16)] = Some mf).
      cbn. rewrite HF. reflexivity.
  - split.
    + erewrite Mem.load_free; [|exact HF|left; congruence].
      eapply load_store64_other_block; [exact SE | congruence |].
      eapply load_store64_same; exact SW.
    + split.
      * erewrite Mem.load_free; [|exact HF|left; congruence].
        eapply load_store64_same; exact SE.
      * intros chunk b ofs HV Hbd Hbw.
        assert (Hbl : b <> bl).
        { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
        erewrite Mem.load_free; [|exact HF|auto].
        erewrite Mem.load_store_other; [|exact SE|auto].
        erewrite Mem.load_store_other; [|exact SW|auto].
        erewrite Mem.load_store_other; [|exact SB|auto].
        erewrite Mem.load_store_other; [|exact SO|auto].
        erewrite Mem.load_store_other; [|exact SR|auto].
        erewrite Mem.load_storebytes_other; [|exact SC|auto].
        eapply Mem.load_alloc_unchanged; eauto.
Qed.

(** Backwards-compatible zero-word corollary. *)
Theorem eval_increment8_concrete m bd bs bi bw w :
  Mem.load Mptr m bs 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bs 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong w) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong Int64.zero) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  bd <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 =
      Some (Vlong (increment8_written_word (read8_result w))) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
    (forall chunk b ofs, Mem.valid_block m b -> b <> bd -> b <> bw ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSE HSO HI HDE HDO HW PD PW HDw.
  destruct (eval_increment8_concrete_word m bd bs bi bw w Int64.zero
    HSE HSO HI HDE HDO HW PD PW HDw) as [mf [HC [HO [HF HP]]]].
  rewrite increment8_word_update_zero in HO.
  exists mf. split; [exact HC |]. split; [exact HO |]. split; assumption.
Qed.
