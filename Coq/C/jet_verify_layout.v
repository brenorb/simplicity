(** Both success and failure of the actual verify jet, at all valid cursors.
    Its destination and ALL pre-existing loads are unchanged in either case.
    The initial-only theorem derives allocation/copy/read/free rather than
    requiring their execution as premises. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate Simplicity.Util.Option.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_encoding C.jet_partial C.jet_assertion_spec C.jet_verify_exec.
Require Import C.jet_constant_layout C.jet_readBit_layout C.jet_writeBit.
Require Import C.jet_clight_determinism.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_verify_layout env m bd dbase bs sbase bi edge bit rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 1 -> frame_input_bit_at m bi edge rc bit ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_verify)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint (bit_int bit)) /\
    (forall chunk b ofs, Mem.valid_block m b -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput as [_ [_ [w [HL _]]]]. eapply fresh_frame_not_loaded; eauto. }
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_loadbytes_at ma bs sbase _ _ HSEa HSOa) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa) as [HLE HLO].
  assert (HInputC : frame_input_bit_at mc bi edge rc bit).
  { destruct Hinput as [HR [HEi [w [HL HX]]]].
    split; [exact HR|]. split; [exact HEi|]. exists w. split; [|exact HX].
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_readBit_layout mc bl 0 bi edge rc bit HLocalBase HRC (conj HLE HLO) HInputC PLC)
    as (mr & Hread & HReadFields & HReadMem & HReadPerm & HReadValid).
  assert (PLE : Mem.range_perm mr bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free mr bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_verify_composes; eauto.
  - intros chunk b ofs HV.
    assert (Hbl : b <> bl).
    { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
    erewrite Mem.load_free; [|exact HF|auto]. rewrite HReadMem by (left; exact Hbl).
    erewrite Mem.load_storebytes_other; [|exact SC|auto].
    eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem verify_silent_guarantees env m bd dbase bs sbase bi edge (x : Ty.tySem Bit) rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 1 -> frame_input_bit_at m bi edge rc (Bit.toBool x) ->
  exists mf,
    silent_call_guarantees ge0 (Internal f_simplicity_verify)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
      m (jet_partial_return (@verify_spec (Alg.AssertionSem option_Monad_Zero) x)) mf /\
    (forall chunk b ofs, Mem.valid_block m b -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HB HA HF HR Hin.
  destruct (eval_verify_layout env m bd dbase bs sbase bi edge (Bit.toBool x) rc
    HB HA HF HR Hin) as (mf & Hcall & Hloads).
  exists mf. split; [|exact Hloads].
  rewrite verify_spec_option.
  destruct x as [u | u]; destruct u;
    exact (eval_funcall_silent_guarantees prog m (Internal f_simplicity_verify) _ mf _ Hcall).
Qed.

Theorem verify_local_spec : jet_partial_local_spec f_simplicity_verify Bit Ty.Unit
  (fun x => @verify_spec (Alg.AssertionSem option_Monad_Zero) x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Bit)) with 1 in Hmax.
  assert (Hbit : frame_input_bit_at m bi edge rc (Bit.toBool x)).
  { specialize (Hin 0%nat (Some (Bit.toBool x)) ltac:(destruct x as [u | u]; destruct u; reflexivity)).
    change (frame_input_bit_at m bi edge (rc + 0) (Bit.toBool x)) in Hin.
    rewrite Z.add_0_r in Hin. exact Hin. }
  destruct (eval_verify_layout env m bd dbase bs sbase bi edge (Bit.toBool x) rc
    HB HA HF ltac:(lia) Hbit) as (mf & Hcall & Hloads).
  assert (HP : forall chunk b ofs v, Mem.load chunk m b ofs = Some v ->
    Mem.load chunk mf b ofs = Some v).
  { intros chunk b ofs v HL. rewrite Hloads; [exact HL|].
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies with (p1 := Readable);
      [eapply Mem.load_valid_access; eauto|constructor]. }
  exists mf. split.
  - rewrite verify_spec_option. destruct x as [u | u]; destruct u; exact Hcall.
  - split.
    + rewrite verify_spec_option. destruct x as [u | u]; destruct u; [exact I|].
      split.
      * intros i c Hnth. destruct i; discriminate Hnth.
      * split.
        -- intros old HL. exists old. split; [eapply HP; exact HL|].
           intros i Hi Houtside. reflexivity.
        -- change (cursor - Z.of_nat (bitSize Ty.Unit)) with (cursor - 0).
           rewrite Z.sub_0_r. destruct Hout as [_ [[HE HC] _]].
           split; eapply HP; eauto.
    + intros chunk b ofs HV _ _. apply Hloads; exact HV.
Qed.
