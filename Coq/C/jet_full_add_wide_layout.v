(** Complete full_add_16/32/64 calls against the canonical carry-input program. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_spec C.jet_full_add_wide_word C.jet_full_add_wide_exec.
Require Import C.jet_carry_wide_layout C.jet_output_slice C.jet_complement_wide_layout C.jet_wide.
Require Import C.jet_readBit_layout C.jet_writeBit_layout_total.

Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_wide_full_add_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge
    (c : Ty.tySem Bit) (x y : Ty.tySem (Word (wide_log s))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - (1 + 2 * wide_bits s) ->
  frame_input_bit_at m bi edge rc (Bit.toBool c) ->
  frame_input_word_at m bi edge (rc + 1) x ->
  frame_input_word_at m bi edge (rc + 1 + wide_bits s) y ->
  write_frame_at m bd dbase bw outedge cursor (1 + wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_full_add s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@wide_full_add_spec s Alg.CoreFunSem (c, (x, y)))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - (1 + wide_bits s)) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - (1 + wide_bits s)) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput1 Hinput2 Hinput3 Hout.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (1 + wide_bits s) ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput1 as [_ [_ [w [HL _]]]]. eapply fresh_frame_not_loaded; eauto. }
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
  assert (HInputC1 : frame_input_bit_at mc bi edge rc (Bit.toBool c)).
  { eapply frame_input_bit_at_preserved; [|exact Hinput1].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC1 : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_readBit_layout mc bl 0 bi edge rc (Bit.toBool c) HLocalBase ltac:(lia)
    (conj HLE HLO) HInputC1 PLC1)
    as (mr & Hread1 & HReadFields1 & HReadMem1 & HReadPerm1 & HReadValid1).
  assert (HInputR2 : frame_input_word_at mr bi edge (rc + 1) x).
  { eapply frame_input_bits_at_preserved; [|exact Hinput2].
    intros ofs w HL. rewrite HReadMem1 by (left; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC2 : Mem.valid_access mr Mint64 bl 8 Writable).
  { destruct PLC1 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm1. apply HP; exact Hrange. }
  destruct (eval_read_wide_word_at s mr bl 0 bi edge (rc + 1) x HLocalBase ltac:(lia)
    HReadFields1 HInputR2 PLC2 HLi)
    as (mr2 & r & Hread2 & Hr & HReadFields2 & HReadMem2 & HReadPerm2 & HReadValid2).
  assert (HInputR3 : frame_input_word_at mr2 bi edge (rc + 1 + wide_bits s) y).
  { eapply frame_input_bits_at_preserved; [|exact Hinput3].
    intros ofs w HL. rewrite HReadMem2 by (left; congruence).
    rewrite HReadMem1 by (left; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC3 : Mem.valid_access mr2 Mint64 bl 8 Writable).
  { destruct PLC2 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm2. apply HP; exact Hrange. }
  destruct (eval_read_wide_word_at s mr2 bl 0 bi edge (rc + 1 + wide_bits s) y HLocalBase ltac:(lia)
    HReadFields2 HInputR3 PLC3 HLi)
    as (mr3 & t & Hread3 & Ht & HReadFields3 & HReadMem3 & HReadPerm3 & HReadValid3).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr3 b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    rewrite HReadMem3 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem2 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem1 by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr3 b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm3. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr3 bd dbase bw outedge cursor (1 + wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_carry_wide_layout s mr3 bd dbase bw outedge cursor
    (wide_full_add_carry s (Bit.toBool c) r t)
    (wide_full_add_payload (Bit.toBool c) r t) HOutR)
    as (mb & me & Hbit & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm3. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_full_add_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w' HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply (carry_wide_output_encode s); [lia|].
        rewrite (wide_full_add_values_denote_input s c x y r t Hr Ht) in Houtput. exact Houtput.
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
           rewrite Hmemory; [|exact Hbd|].
           2: { pose proof (slice_write_low_bound (wide_bits s) outedge (cursor - 1) ltac:(lia) ltac:(lia)) as Hlow.
                replace (cursor - 1 - wide_bits s) with (cursor - (1 + wide_bits s)) in Hlow by lia.
                destruct Hbw as [Hbw|[Hbw|Hbw]]; [left|right; left|right; right]; auto; lia. }
           rewrite HReadMem3 by (left; exact Hbl).
           rewrite HReadMem2 by (left; exact Hbl).
           rewrite HReadMem1 by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem wide_full_add_local_spec s : jet_local_spec (wide_full_add s)
  (Ty.Prod Bit (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))) (Ty.Prod Bit (Word (wide_log s)))
  (fun cxy => @wide_full_add_spec s Alg.CoreFunSem cxy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [c [x y]] HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod Bit (Ty.Prod (Word (wide_log s)) (Word (wide_log s))))))
    with (1 + 2 * wide_bits s) in Hmax by (destruct s; reflexivity).
  replace (Z.of_nat (bitSize (Ty.Prod Bit (Word (wide_log s)))))
    with (1 + wide_bits s) in * by (destruct s; reflexivity).
  change (frame_input_cells_at m bi edge rc (encode c ++ (encode x ++ encode y))) in Hin.
  rewrite frame_input_cells_at_app in Hin.
  assert (Hlen : length (encode c) = 1%nat) by (destruct c as [[]|[]]; reflexivity).
  rewrite Hlen in Hin. change (Z.of_nat 1) with 1 in Hin.
  destruct Hin as [Hcin Hxy]. rewrite frame_input_cells_at_app in Hxy.
  assert (Hlenx : Z.of_nat (length (encode x)) = wide_bits s).
  { rewrite encode_length. destruct s; reflexivity. }
  rewrite Hlenx in Hxy. destruct Hxy as [Hx Hy].
  eapply eval_wide_full_add_layout_matches_spec; eauto; [lia| | |].
  - specialize (Hcin 0%nat (Some (Bit.toBool c)) ltac:(destruct c as [[]|[]]; reflexivity)).
    change (frame_input_bit_at m bi edge (rc + 0) (Bit.toBool c)) in Hcin.
    rewrite Z.add_0_r in Hcin. exact Hcin.
  - apply frame_input_word_at_encode. exact Hx.
  - apply frame_input_word_at_encode. exact Hy.
Qed.
Corollary full_add16_local_spec : jet_local_spec f_simplicity_full_add_16
  (Ty.Prod Bit (Ty.Prod (Word 4) (Word 4))) (Ty.Prod Bit (Word 4))
  (fun cxy => @wide_full_add_spec W16 Alg.CoreFunSem cxy).
Proof. exact (wide_full_add_local_spec W16). Qed.
Corollary full_add32_local_spec : jet_local_spec f_simplicity_full_add_32
  (Ty.Prod Bit (Ty.Prod (Word 5) (Word 5))) (Ty.Prod Bit (Word 5))
  (fun cxy => @wide_full_add_spec W32 Alg.CoreFunSem cxy).
Proof. exact (wide_full_add_local_spec W32). Qed.
Corollary full_add64_local_spec : jet_local_spec f_simplicity_full_add_64
  (Ty.Prod Bit (Ty.Prod (Word 6) (Word 6))) (Ty.Prod Bit (Word 6))
  (fun cxy => @wide_full_add_spec W64 Alg.CoreFunSem cxy).
Proof. exact (wide_full_add_local_spec W64). Qed.
Theorem wide_full_add_context s : jet_context_for (wide_full_add s) (@wide_full_add_spec s).
Proof.
  exact (jet_context _ _ (wide_full_add_spec_parametric s) (wide_full_add_local_spec s)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_full_add_guarantees s := jet_local_spec_guarantees _ _ _ _ (wide_full_add_local_spec s).
Definition wide_full_add_context_guarantees s :=
  jet_context_guarantees _ _ (wide_full_add_spec_parametric s) (wide_full_add_local_spec s)
    ltac:(destruct s; vm_compute; lia).
