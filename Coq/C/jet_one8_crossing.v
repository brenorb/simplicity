(** Complete C-to-Simplicity one_8 theorem on all two-word crossing splits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_one8 C.jet_frame_copy C.jet_spec C.jets.
Require Import C.jet_frame_spec C.jet_word_bits C.jet_crossing_word C.jet_write8_crossing.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_one8_crossing_matches_spec m bd bs bw bytes k :
  1 <= k <= 7 ->
  Mem.loadbytes m bs 0 16 = Some bytes ->
  write_frame m bd bw 0 (64 + k) 8 ->
  exists mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    decode_word8 (crossing_byte k high low) = @one8_spec Alg.CoreFunSem tt /\
    (forall old, Mem.load Mint64 m bw 8 = Some (Vlong old) ->
      word_outside_eq 0 k high old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HK HB HFrame.
  destruct (crossing_frame_words m bd bw k HK HFrame)
    as [[HE HO] [HDw [PD [PH [PW [oldhigh [oldlow [HH HW]]]]]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HBa : Mem.loadbytes ma bs 0 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [exact HB | exact HA |].
    eapply Mem.perm_valid_block.
    eapply (Mem.loadbytes_range_perm _ _ _ _ _ HB 0). lia. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange | constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  assert (HEc : Mem.load Mptr mc bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HOc : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr (64 + k)))).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HHc : Mem.load Mint64 mc bw 8 = Some (Vlong oldhigh)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HWc : Mem.load Mint64 mc bw 0 = Some (Vlong oldlow)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (PDc : Mem.valid_access mc Mint64 bd 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  assert (PHc : Mem.valid_access mc Mint64 bw 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  assert (PWc : Mem.valid_access mc Mint64 bw 0 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  destruct (Mem.valid_access_store mc Mint64 bw 8 (Vlong (clear_low k oldhigh)) PHc)
    as [mh SH].
  assert (PDh : Mem.valid_access mh Mint64 bd 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mh Mint64 bd 8 (Vlong (Int64.repr 64)) PDh)
    as [mo SO].
  assert (PWo : Mem.valid_access mo Mint64 bw 0 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mo Mint64 bw 0
    (Vlong (Int64.shl Int64.one (Int64.repr (56 + k)))) PWo) as [mw SW].
  assert (PDw : Mem.valid_access mw Mint64 bd 8 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong (Int64.repr (56 + k))) PDw)
    as [me SE].
  assert (PLe : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange.
    eapply Mem.perm_store_1; [exact SE |].
    eapply Mem.perm_store_1; [exact SW |].
    eapply Mem.perm_store_1; [exact SO |].
    eapply Mem.perm_store_1; [exact SH |].
    eapply Mem.perm_storebytes_1; [exact SC |].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLe) as [mf HF].
  assert (HFlist : Mem.free_list me (blocks_of_env ge0 (e_one8 bl)) = Some mf).
  { change (Mem.free_list me [(bl, 0, 16)] = Some mf).
    cbn. rewrite HF. reflexivity. }
  assert (Hwrite : ClightBigstep.Clight2.eval_funcall ge0 mc
      (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint Int.one] E0 me Vundef).
  { eapply eval_write8_crossing_one; eauto. }
  assert (HC : ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef] E0 mf (Vint Int.one)).
  { eapply eval_one8 with (m1 := ma) (m2 := mc) (m3 := me)
      (bl := bl) (bytes := bytes).
    - exact HA.
    - reflexivity.
    - intros _. exists 0; reflexivity.
    - intros _. exists 0; reflexivity.
    - right; left; reflexivity.
    - exact HBa.
    - exact SC.
    - exact Hwrite.
    - exact HFlist. }
  exists mf, (clear_low k oldhigh), (Int64.shl Int64.one (Int64.repr (56 + k))).
  split; [exact HC |].
  split.
  - erewrite Mem.load_free; [|exact HF|auto].
    erewrite Mem.load_store_other; [|exact SE|auto].
    erewrite Mem.load_store_other; [|exact SW|right; right; cbn; lia].
    erewrite Mem.load_store_other; [|exact SO|auto].
    exact (Mem.load_store_same _ _ _ _ _ _ SH).
  - split.
    + erewrite Mem.load_free; [|exact HF|auto].
      erewrite Mem.load_store_other; [|exact SE|auto].
      exact (Mem.load_store_same _ _ _ _ _ _ SW).
    + split; [apply crossing_byte_one; exact HK |].
      split.
      * intros old HH'. assert (old = oldhigh) by congruence. subst old.
        apply clear_low_prefix; lia.
      * split.
        -- erewrite Mem.load_free; [|exact HF|auto].
           exact (Mem.load_store_same _ _ _ _ _ _ SE).
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           erewrite Mem.load_store_other; [|exact SE|auto].
           erewrite Mem.load_store_other; [|exact SW|auto].
           erewrite Mem.load_store_other; [|exact SO|auto].
           erewrite Mem.load_store_other; [|exact SH|auto].
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.
