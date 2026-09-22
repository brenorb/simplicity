(** Full increment equivalence on all eight crossing output splits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_read8_position.
Require Import C.jet_increment8 C.jet_increment8_exec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_increment8_spec C.jet_increment8_word C.jet_input_position.
Require Import C.jet_crossing_frame C.jet_carry_byte_crossing C.jet_increment8_crossing_word.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem eval_increment8_crossing_matches_spec m bd bs bi bw (x : Ty.tySem Word8) k read_cursor :
  0 <= k <= 7 ->
  single_word_input_at m bs bi read_cursor (encode_word8 x) ->
  write_frame m bd bw 0 (65 + k) 9 ->
  exists mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef] E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    decode_carry_crossing k high low = @increment8_spec Alg.CoreFunSem x /\
    (forall old, Mem.load Mint64 m bw 8 = Some (Vlong old) ->
      word_outside_eq 0 (k + 1) high old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HK HInput HOutput.
  destruct (single_word_input_at_decode m bs bi read_cursor x HInput)
    as [w [[HSE HSO] [HRead [HI Hdecode]]]].
  destruct (crossing_carry_frame_words m bd bw k HK HOutput)
    as [[HDE HDO] [HDw [PD [PH [PW [oldhigh [oldlow [HH HW]]]]]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs 0 = Some (Vptr bi (Ptrofs.repr 8)))
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
  assert (HIC : Mem.load Mint64 mc bi 0 = Some (Vlong w)).
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
  destruct (Mem.valid_access_store mc Mint64 bl 8 (Vlong (Int64.repr (read_cursor + 8))) PLC)
    as [mr SR].
  assert (HDEr : Mem.load Mptr mr bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; eauto).
  assert (HDOr : Mem.load Mint64 mr bd 8 = Some (Vlong (Int64.repr (65 + k))))
    by (eapply load_store64_other_block; eauto).
  assert (HHr : Mem.load Mint64 mr bw 8 = Some (Vlong oldhigh))
    by (eapply load_store64_other_block; eauto).
  assert (HWr : Mem.load Mint64 mr bw 0 = Some (Vlong oldlow))
    by (eapply load_store64_other_block; eauto).
  assert (PDr : Mem.valid_access mr Mint64 bd 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  assert (PHr : Mem.valid_access mr Mint64 bw 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  assert (PWr : Mem.valid_access mr Mint64 bw 0 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  set (r := read8_at read_cursor w).
  set (carry := Int.ltu (Int.sub (Int.repr 255) (Int.repr 1)) (increment8_u r)).
  destruct (eval_carry_byte_crossing mr bd bw k carry (increment8_byte r) oldhigh oldlow HK
    (conj HDEr HDOr) HDw PDr PHr PWr HHr HWr)
    as [mb [me [high [low [Hbit [Hwrite [HHout [HLout [Hcarry [Hbyte [Hprefix [Hoff [Hmem Hperm]]]]]]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm.
    eapply Mem.perm_store_1; [exact SR |].
    eapply Mem.perm_storebytes_1; [exact SC |]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf, high, low. split.
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
        -- eapply eval_read8_position; eauto.
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
    + erewrite Mem.load_free; [exact HHout|exact HF|auto].
    + split.
      * erewrite Mem.load_free; [exact HLout|exact HF|auto].
      * split.
        -- unfold decode_carry_crossing. rewrite Hcarry, Hbyte.
           unfold carry, r, read8_at.
           rewrite increment8_carry_byte_spec, Hdecode. reflexivity.
        -- split.
           ++ intros old HOld. assert (old = oldhigh) by congruence. subst old. exact Hprefix.
           ++ split.
              ** erewrite Mem.load_free; [exact Hoff|exact HF|auto].
              ** intros chunk b ofs HV Hbd Hbw.
                 assert (Hbl : b <> bl).
                 { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
                 erewrite Mem.load_free; [|exact HF|auto].
                 rewrite Hmem; [|eauto using Mem.store_valid_block_1,
                   Mem.storebytes_valid_block_1, Mem.valid_block_alloc|exact Hbd|exact Hbw].
                 erewrite Mem.load_store_other; [|exact SR|auto].
                 erewrite Mem.load_storebytes_other; [|exact SC|auto].
                 eapply Mem.load_alloc_unchanged; eauto.
Qed.

