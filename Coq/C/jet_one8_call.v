(** Total [one_8] execution from initial-memory facts, including the by-value
    source-frame copy even though the Simplicity input is Unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_one8 C.jet_increment8_call C.jet_spec jets.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Theorem eval_one8_initial_matches_spec m bd bs bw bytes :
  Mem.loadbytes m bs 0 16 = Some bytes ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong Int64.zero) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  bd <> bw ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_word8 output = @one8_spec Alg.CoreFunSem tt /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero).
Proof.
  intros HB HE HO HW PD PW HDw.
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
  assert (HOc : Mem.load Mint64 mc bd 8 = Some (Vlong (Int64.repr 8))).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (HWc : Mem.load Mint64 mc bw 0 = Some (Vlong Int64.zero)).
  { erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto | exact SC | auto]. }
  assert (PDc : Mem.valid_access mc Mint64 bd 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  assert (PWc : Mem.valid_access mc Mint64 bw 0 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC |].
    eapply Mem.valid_access_alloc_other; eauto. }
  destruct (Mem.valid_access_store mc Mint64 bw 0 (Vlong Int64.one) PWc)
    as [mw SW].
  assert (PDw : Mem.valid_access mw Mint64 bd 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong Int64.zero) PDw)
    as [me SE].
  assert (PLe : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange.
    eapply Mem.perm_store_1; [exact SE |].
    eapply Mem.perm_store_1; [exact SW |].
    eapply Mem.perm_storebytes_1; [exact SC |].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLe) as [mf HF].
  assert (HFlist : Mem.free_list me (blocks_of_env ge0 (e_one8 bl)) = Some mf).
  { change (Mem.free_list me [(bl, 0, 16)] = Some mf).
    cbn. rewrite HF. reflexivity. }
  assert (Hrun : Mem.load Mint64 mf bw 0 = Some (Vlong Int64.one) /\
      Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
      ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_one_8)
        [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef] E0 mf (Vint Int.one)).
  { eapply eval_one8_zero with (m1 := ma) (m2 := mc) (mw := mw)
      (m3 := me) (bl := bl) (bytes := bytes).
    - exact HA.
    - reflexivity.
    - intros _. exists 0; reflexivity.
    - intros _. exists 0; reflexivity.
    - right; left; reflexivity.
    - exact HBa.
    - exact SC.
    - exact HEc.
    - exact HOc.
    - exact HWc.
    - exact SW.
    - exact SE.
    - exact HDw.
    - exact HLd.
    - exact HLw.
    - exact HFlist. }
  destruct Hrun as [Hout [Hoff HC]].
  exists mf, Int64.one.
  split; [exact HC |]. split; [exact Hout |].
  split; [apply decode_word8_one | exact Hoff].
Qed.
