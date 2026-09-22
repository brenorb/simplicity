(** Full add equivalence on all eight crossing output splits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_read8_position.
Require Import C.jet_add8 C.jet_add8_exec C.jet_increment8_exec C.jet_frame_copy C.jet_frame_spec.
Require Import C.jet_add8_spec C.jet_increment8_spec.
Require Import C.jet_crossing_frame C.jet_carry_byte_crossing C.jet_increment8_crossing_word C.jet_add8_word.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Theorem eval_add8_crossing_matches_spec m bd bs bi bw (x y : Ty.tySem Word8) k read_cursor :
  0 <= k <= 7 ->
  single_word_pair_input_at m bs bi read_cursor x y ->
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
  destruct HInput as [[HSE HSO] [HRead [w [HI [HX HY]]]]].
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
  assert (PLR : Mem.valid_access mr Mint64 bl 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mr Mint64 bl 8 (Vlong (Int64.repr (read_cursor + 16))) PLR)
    as [mr2 SR2].
  assert (HDEr : Mem.load Mptr mr2 bd 0 = Some (Vptr bw Ptrofs.zero))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (HDOr : Mem.load Mint64 mr2 bd 8 = Some (Vlong (Int64.repr (65 + k))))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (HHr : Mem.load Mint64 mr2 bw 8 = Some (Vlong oldhigh))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (HWr : Mem.load Mint64 mr2 bw 0 = Some (Vlong oldlow))
    by (eapply load_store64_other_block; [exact SR2 | auto |]; eapply load_store64_other_block; eauto).
  assert (PDr : Mem.valid_access mr2 Mint64 bd 8 Writable)
    by (eauto using Mem.store_valid_access_1).
  assert (PHr : Mem.valid_access mr2 Mint64 bw 8 Writable)
    by (eauto using Mem.store_valid_access_1).
  assert (PWr : Mem.valid_access mr2 Mint64 bw 0 Writable)
    by (eauto using Mem.store_valid_access_1).
  set (r := read8_at read_cursor w).
  set (s := read8_at (read_cursor + 8) w).
  set (carry := Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)).
  destruct (eval_carry_byte_crossing mr2 bd bw k carry (add8_byte r s) oldhigh oldlow HK
    (conj HDEr HDOr) HDw PDr PHr PWr HHr HWr)
    as [mb [me [high [low [Hbit [Hwrite [HHout [HLout [Hcarry [Hbyte [Hprefix [Hoff [Hmem Hperm]]]]]]]]]]]]].
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm.
    eapply Mem.perm_store_1; [exact SR2 |].
    eapply Mem.perm_store_1; [exact SR |].
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
        -- eapply eval_read8_position; eauto; lia.
      * eapply call_add8_read.
        -- apply symbol_read8.
        -- apply funct_read8.
        -- eapply eval_read8_position.
           ++ lia.
           ++ eapply load_edge_store_offset; eauto.
           ++ eapply load_store64_same; eauto.
           ++ eapply load_store64_other_block; eauto.
           ++ replace (read_cursor + 8 + 8) with (read_cursor + 16) by lia. exact SR2.
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
           unfold carry, r, s, read8_at.
           rewrite add8_values_denote_spec.
           rewrite (word8_payload_at_decode _ _ _ HX), (word8_payload_at_decode _ _ _ HY).
           reflexivity.
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
                 erewrite Mem.load_store_other; [|exact SR2|auto].
                 erewrite Mem.load_store_other; [|exact SR|auto].
                 erewrite Mem.load_storebytes_other; [|exact SC|auto].
                 eapply Mem.load_alloc_unchanged; eauto.
Qed.


