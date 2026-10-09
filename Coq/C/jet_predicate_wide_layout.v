(** Complete wide some/all implementation-to-Simplicity calls, deriving
    all reads, bit writes and frame cleanup from initial contracts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_wide C.jet_complement_wide_layout C.jet_writeBit_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_predicate_spec C.jet_predicate_wide_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_wide_predicate_layout_matches_spec env s all m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem (Word (wide_log s))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - wide_bits s -> frame_input_word_at m bi edge rc x ->
  write_frame_at m bd dbase bw outedge cursor 1 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_predicate s all))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@predicate_spec (wide_log s) all Alg.CoreFunSem x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 1) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 1) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 1 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct (wide_input_first_load s m bi edge rc x Hinput) as [w HL].
    eapply fresh_frame_not_loaded; eauto. }
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
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
  assert (HInputC : frame_input_word_at mc bi edge rc x).
  { eapply frame_input_bits_at_preserved; [|exact Hinput].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_read_wide_word_at s mc bl 0 bi edge rc x HLocalBase HRC (conj HLE HLO) HInputC PLC HLi)
    as (mr & r & Hread & Hr & HReadFields & HReadMem & HReadPerm & HReadValid).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v Hb HL. rewrite HReadMem by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_writeBit_layout mr bd dbase bw outedge cursor (wide_predicate_bit s all r) HOutR)
    as (me & w & Hwrite & Hload & Hbit & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_predicate_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply carry_output_encode; [lia|]. exists w. split; [exact Hload|].
        rewrite Hbit, (wide_predicate_denotes s all x r Hr).
        destruct (@predicate_spec (wide_log s) all Alg.CoreFunSem x) as [[]|[]]; reflexivity.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w' HL. eapply HBeforeLoad; eauto.
        -- intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption. rewrite HReadMem by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem wide_predicate_local_spec s all :
  jet_local_spec (wide_predicate s all) (Word (wide_log s)) Bit
    (fun x => @predicate_spec (wide_log s) all Alg.CoreFunSem x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in Hmax by (destruct s; reflexivity).
  change (Z.of_nat (bitSize Bit)) with 1 in Hout.
  apply frame_input_word_at_encode in Hin.
  exact (eval_wide_predicate_layout_matches_spec env s all m bd dbase bs sbase bi bw edge outedge x
    cursor rc HB HA HF ltac:(lia) Hin Hout).
Qed.
Corollary some16_local_spec : jet_local_spec f_simplicity_some_16 (Word 4) Bit
  (fun x => @predicate_spec 4 Datatypes.false Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W16 Datatypes.false). Qed.
Corollary some32_local_spec : jet_local_spec f_simplicity_some_32 (Word 5) Bit
  (fun x => @predicate_spec 5 Datatypes.false Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W32 Datatypes.false). Qed.
Corollary some64_local_spec : jet_local_spec f_simplicity_some_64 (Word 6) Bit
  (fun x => @predicate_spec 6 Datatypes.false Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W64 Datatypes.false). Qed.
Corollary all16_local_spec : jet_local_spec f_simplicity_all_16 (Word 4) Bit
  (fun x => @predicate_spec 4 Datatypes.true Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W16 Datatypes.true). Qed.
Corollary all32_local_spec : jet_local_spec f_simplicity_all_32 (Word 5) Bit
  (fun x => @predicate_spec 5 Datatypes.true Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W32 Datatypes.true). Qed.
Corollary all64_local_spec : jet_local_spec f_simplicity_all_64 (Word 6) Bit
  (fun x => @predicate_spec 6 Datatypes.true Alg.CoreFunSem x).
Proof. exact (wide_predicate_local_spec W64 Datatypes.true). Qed.
Theorem wide_predicate_context s all : jet_context_for (wide_predicate s all) (@predicate_spec (wide_log s) all).
Proof.
  exact (jet_context _ _ (predicate_spec_parametric (wide_log s) all) (wide_predicate_local_spec s all)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_predicate_guarantees s all := jet_local_spec_guarantees _ _ _ _ (wide_predicate_local_spec s all).
Definition wide_predicate_context_guarantees s all :=
  jet_context_guarantees _ _ (predicate_spec_parametric (wide_log s) all) (wide_predicate_local_spec s all)
    ltac:(destruct s; vm_compute; lia).
