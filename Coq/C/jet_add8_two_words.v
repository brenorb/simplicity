(** Full add equivalence with arbitrary two-word input alignment and crossing output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_read8_position.
Require Import C.jet_add8 C.jet_add8_exec C.jet_increment8_exec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_add8_spec C.jet_add8_word C.jet_input_position C.jet_two_word_input C.jet_read8_two_words.
Require Import C.jet_crossing_frame C.jet_carry_byte_crossing C.jet_increment8_crossing_word.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem eval_add8_two_words_matches_spec m bd bs bi bw (x y : Ty.tySem Word8) k read_cursor :
  0 <= k <= 7 ->
  two_word_input m bs bi read_cursor [x; y] ->
  write_frame m bd bw 0 (65 + k) 9 ->
  exists mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_add_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef] E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    decode_carry_crossing k high low = @add8_spec Alg.CoreFunSem (x, y) /\
    (forall old, Mem.load Mint64 m bw 8 = Some (Vlong old) ->
      word_outside_eq 0 (k + 1) high old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HK HInput HOutput.
  destruct (two_word_input_pair m bs bi read_cursor x y HInput)
    as [inputhigh [inputlow [[HSE HSO] [HRead [HIH [HIL [Hdecode HdecodeY]]]]]]].
  destruct (crossing_carry_frame_words m bd bw k HK HOutput)
    as [[HDE HDO] [HDw [PD [PH [PW [oldhigh [oldlow [HH HW]]]]]]]].
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
  assert (HDEC : Mem.load Mptr mc bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HDOC : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr (65 + k)))).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HWC : Mem.load Mint64 mc bw 0 = Some (Vlong oldlow)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HHC : Mem.load Mint64 mc bw 8 = Some (Vlong oldhigh)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (PHC : Mem.valid_access mc Mint64 bw 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
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
  destruct (eval_read8_two_words mc bl bi read_cursor inputhigh inputlow ltac:(lia)
    (conj HLE HLO) HIHC HILC PLC HLi)
    as [mr [Hread [HReadFields [HReadMem [HReadPerm HReadValid]]]]].
  assert (PHIr : Mem.load Mint64 mr bi 8 = Some (Vlong inputhigh))
    by (rewrite HReadMem by congruence; exact HIHC).
  assert (PLIr : Mem.load Mint64 mr bi 0 = Some (Vlong inputlow))
    by (rewrite HReadMem by congruence; exact HILC).
  assert (PLR : Mem.valid_access mr Mint64 bl 8 Writable)
    by (eapply permissions_preserve_access; eauto).
  destruct (eval_read8_two_words mr bl bi (read_cursor + 8) inputhigh inputlow ltac:(lia)
    HReadFields PHIr PLIr PLR HLi)
    as [mr2 [Hread2 [HReadFields2 [HReadMem2 [HReadPerm2 HReadValid2]]]]].
  assert (HDEr : Mem.load Mptr mr2 bd 0 = Some (Vptr bw Ptrofs.zero))
    by (rewrite HReadMem2 by congruence; rewrite HReadMem by congruence; assumption).
  assert (HDOr : Mem.load Mint64 mr2 bd 8 = Some (Vlong (Int64.repr (65 + k))))
    by (rewrite HReadMem2 by congruence; rewrite HReadMem by congruence; assumption).
  assert (HHr : Mem.load Mint64 mr2 bw 8 = Some (Vlong oldhigh))
    by (rewrite HReadMem2 by congruence; rewrite HReadMem by congruence; assumption).
  assert (HWr : Mem.load Mint64 mr2 bw 0 = Some (Vlong oldlow))
    by (rewrite HReadMem2 by congruence; rewrite HReadMem by congruence; assumption).
  assert (PDr : Mem.valid_access mr2 Mint64 bd 8 Writable)
    by (eapply permissions_preserve_access; [exact HReadPerm2 |]; eapply permissions_preserve_access; eauto).
  assert (PHr : Mem.valid_access mr2 Mint64 bw 8 Writable)
    by (eapply permissions_preserve_access; [exact HReadPerm2 |]; eapply permissions_preserve_access; eauto).
  assert (PWr : Mem.valid_access mr2 Mint64 bw 0 Writable)
    by (eapply permissions_preserve_access; [exact HReadPerm2 |]; eapply permissions_preserve_access; eauto).
  set (r := read8_result (two_word_byte read_cursor inputhigh inputlow)).
  set (s := read8_result (two_word_byte (read_cursor + 8) inputhigh inputlow)).
  set (carry := Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)).
  destruct (eval_carry_byte_crossing mr2 bd bw k carry (add8_byte r s) oldhigh oldlow HK
    (conj HDEr HDOr) HDw PDr PHr PWr HHr HWr)
    as [mb [me [high [low [Hbit [Hwrite [HHout [HLout [Hcarry [Hbyte [Hprefix [Hoff [Hmem Hperm]]]]]]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm.
    apply HReadPerm2. apply HReadPerm.
    eapply Mem.perm_storebytes_1; [exact SC |]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf, high, low. split.
  - eapply ClightBigstep.eval_funcall_internal
      with (e := e_add8 bl) (le1 := le_add8 bd bs Ptrofs.zero)
        (m1 := ma) (le2 := le_add8_ready bd bs Ptrofs.zero r s)
        (m2 := me) (out := Out_return (Some (Vint Int.one, tint)))
        (vres := Vint Int.one).
    + apply entry_add8; exact HA.
    + eapply add8_body_composes.
      * eapply exec_add8_copy with (bytes := bytes).
        -- reflexivity.
        -- intros _. exists 0; reflexivity.
        -- intros _. exists 0; reflexivity.
        -- left; exact HLs.
        -- exact HB.
        -- exact SC.
      * eapply call_add8_read.
        -- apply symbol_read8.
        -- apply funct_read8.
        -- exact Hread.
      * eapply call_add8_read.
        -- apply symbol_read8.
        -- apply funct_read8.
        -- exact Hread2.
      * eapply call_add8_writeBit with (bit := add8_carry_bit r s)
          (vret := Vint (add8_carry_bit r s)).
        -- reflexivity.
        -- apply eval_add8_carry.
        -- apply cast_add8_carry.
        -- apply symbol_writeBit.
        -- apply funct_writeBit.
        -- exact Hbit.
      * eapply call_add8_write with (x := add8_byte r s).
        -- reflexivity.
        -- apply eval_add8_sum.
        -- apply cast_add8_sum.
        -- apply symbol_write8.
        -- apply funct_write8.
        -- exact Hwrite.
    + cbn; split; [discriminate | reflexivity].
    + change (Mem.free_list me [(bl, 0, 16)] = Some mf).
      cbn. rewrite HF. reflexivity.
  - split.
    + erewrite Mem.load_free; [exact HHout|exact HF|auto].
    + split.
      * erewrite Mem.load_free; [exact HLout|exact HF|auto].
      * split.
        -- unfold decode_carry_crossing. rewrite Hcarry, Hbyte.
           unfold carry, r, s.
           rewrite add8_values_denote_spec, Hdecode, HdecodeY. reflexivity.
        -- split.
           ++ intros old HOld. assert (old = oldhigh) by congruence. subst old. exact Hprefix.
           ++ split.
              ** erewrite Mem.load_free; [exact Hoff|exact HF|auto].
              ** intros chunk b ofs HV Hbd Hbw.
                 assert (Hbl : b <> bl).
                 { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
                 erewrite Mem.load_free; [|exact HF|auto].
                 rewrite Hmem; [|apply HReadValid2; apply HReadValid; eauto using Mem.storebytes_valid_block_1,
                   Mem.valid_block_alloc|exact Hbd|exact Hbw].
                 rewrite HReadMem2 by exact Hbl.
                 rewrite HReadMem by exact Hbl.
                 erewrite Mem.load_storebytes_other; [|exact SC|auto].
                 eapply Mem.load_alloc_unchanged; eauto.
Qed.


