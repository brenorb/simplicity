(** Complete div_mod_16/32/64 against canonical quotient/remainder programs,
    reusing the checked two-writer sequencing contract at arbitrary layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_output_slice C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_complement_wide_layout C.jet_word_repr C.jet_complement_spec.
Require Import C.jet_division_value C.jet_divmod_wide_exec C.jet_minmax_wide_layout C.jet_predicate_spec.
Require Import C.jet_division_wide_layout_machine C.jet_divmod_representation C.jet_division_core_spec.
Require Import C.jet_write_wide_sequence.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_wide_divmod_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge
    (x y : Ty.tySem (Word (wide_log s))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 2 * wide_bits s ->
  frame_input_word_at m bi edge rc x -> frame_input_word_at m bi edge (rc + wide_bits s) y ->
  write_frame_at m bd dbase bw outedge cursor (2 * wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_divmod s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@div_mod_word_spec (wide_log s) Alg.CoreFunSem (x,y))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 2 * wide_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 2 * wide_bits s) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput1 Hinput2 Hout.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (2 * wide_bits s) ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct (wide_input_first_load s m bi edge rc x Hinput1) as [w HL].
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
  assert (HCopyLoad : forall ofs w, Mem.load Mint64 m bi ofs = Some (Vlong w) ->
    Mem.load Mint64 mc bi ofs = Some (Vlong w)).
  { intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HInputC1 : frame_input_word_at mc bi edge rc x).
  { eapply frame_input_bits_at_preserved; eauto. }
  assert (HInputC2 : frame_input_word_at mc bi edge (rc + wide_bits s) y).
  { eapply frame_input_bits_at_preserved; eauto. }
  assert (PLC1 : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_read_wide_word_at s mc bl 0 bi edge rc x HLocalBase ltac:(lia) (conj HLE HLO) HInputC1 PLC1 HLi)
    as (mr & r & Hread1 & Hr & HReadFields1 & HReadMem1 & HReadPerm1 & HReadValid1).
  assert (HInputR2 : frame_input_word_at mr bi edge (rc + wide_bits s) y).
  { eapply frame_input_bits_at_preserved; [|exact HInputC2].
    intros ofs w HL. rewrite HReadMem1 by (left; congruence). exact HL. }
  assert (PLC2 : Mem.valid_access mr Mint64 bl 8 Writable).
  { destruct PLC1 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm1. apply HP; exact Hrange. }
  destruct (eval_read_wide_word_at s mr bl 0 bi edge (rc + wide_bits s) y HLocalBase ltac:(lia)
    HReadFields1 HInputR2 PLC2 HLi)
    as (mr2 & t & Hread2 & Ht & HReadFields2 & HReadMem2 & HReadPerm2 & HReadValid2).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr2 b ofs = Some v).
  { intros chunk b ofs v Hb HL.
    rewrite HReadMem2 by (left; destruct Hb; subst; congruence).
    rewrite HReadMem1 by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr2 b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr2 bd dbase bw outedge cursor (2 * wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  assert (HOutPair : write_frame_at mr2 bd dbase bw outedge cursor
    (wide_bits s * Z.of_nat (length [division_wide_raw Datatypes.false r t; division_wide_raw Datatypes.true r t]))).
  { change (write_frame_at mr2 bd dbase bw outedge cursor (wide_bits s * 2)).
    replace (wide_bits s * 2) with (2 * wide_bits s) by lia. exact HOutR. }
  destruct (write_wide_sequence_run_layout s mr2 bd dbase bw outedge cursor
    [division_wide_raw Datatypes.false r t; division_wide_raw Datatypes.true r t] HOutPair)
    as (me & Hrun & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  replace (wide_bits s * Z.of_nat (length [division_wide_raw Datatypes.false r t; division_wide_raw Datatypes.true r t]))
    with (2 * wide_bits s) in Hfields, Hmemory by (cbn [length]; lia).
  cbn [write_wide_sequence_run] in Hrun.
  destruct Hrun as (mq & HwriteQ & lastmem & HwriteR & Hdone). subst lastmem.
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_divmod_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * change (frame_output_cells_at me bw outedge cursor
          (encode (decode_wide s (Int64.zero_ext (wide_bits s) (division_wide_raw Datatypes.false r t))) ++
           encode (decode_wide s (Int64.zero_ext (wide_bits s) (division_wide_raw Datatypes.true r t))) ++ [])) in Houtput.
        rewrite app_nil_r,
          (wide_division_decode Datatypes.false s x y r t Hr Ht),
          (wide_division_decode Datatypes.true s x y r t Hr Ht) in Houtput.
        change (frame_output_cells_at me bw outedge cursor
          (@encode (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))
            (@fromZ (WordToZ (wide_log s)) (division_numeric Datatypes.false (@toZ (WordToZ (wide_log s)) x) (@toZ (WordToZ (wide_log s)) y)),
             @fromZ (WordToZ (wide_log s)) (division_numeric Datatypes.true (@toZ (WordToZ (wide_log s)) x) (@toZ (WordToZ (wide_log s)) y))))) in Houtput.
        rewrite div_mod_word_representation in Houtput. exact Houtput.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. eapply HBeforeLoad; eauto.
        -- intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption.
           rewrite HReadMem2 by (left; exact Hbl). rewrite HReadMem1 by (left; exact Hbl).
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.

Theorem wide_divmod_local_spec s : jet_local_spec (wide_divmod s)
  (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))
  (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))
  (fun xy => @div_mod_word_spec (wide_log s) Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))))
    with (2 * wide_bits s) in * by (destruct s; reflexivity).
  apply frame_input_word_pair_encode in Hin. rewrite <- wide_bits_pow in Hin.
  destruct Hin as [HX HY]. eapply eval_wide_divmod_layout_matches_spec; eauto; lia.
Qed.
Corollary divmod16_local_spec : jet_local_spec f_simplicity_div_mod_16
  (Ty.Prod (Word 4) (Word 4)) (Ty.Prod (Word 4) (Word 4))
  (fun xy => @div_mod_word_spec 4 Alg.CoreFunSem xy).
Proof. exact (wide_divmod_local_spec W16). Qed.
Corollary divmod32_local_spec : jet_local_spec f_simplicity_div_mod_32
  (Ty.Prod (Word 5) (Word 5)) (Ty.Prod (Word 5) (Word 5))
  (fun xy => @div_mod_word_spec 5 Alg.CoreFunSem xy).
Proof. exact (wide_divmod_local_spec W32). Qed.
Corollary divmod64_local_spec : jet_local_spec f_simplicity_div_mod_64
  (Ty.Prod (Word 6) (Word 6)) (Ty.Prod (Word 6) (Word 6))
  (fun xy => @div_mod_word_spec 6 Alg.CoreFunSem xy).
Proof. exact (wide_divmod_local_spec W64). Qed.
Theorem wide_divmod_context s : jet_context_for (wide_divmod s) (@div_mod_word_spec (wide_log s)).
Proof.
  exact (jet_context _ _ (div_mod_word_spec_parametric (wide_log s)) (wide_divmod_local_spec s)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_divmod_guarantees s := jet_local_spec_guarantees _ _ _ _ (wide_divmod_local_spec s).
Definition wide_divmod_context_guarantees s :=
  jet_context_guarantees _ _ (div_mod_word_spec_parametric (wide_log s)) (wide_divmod_local_spec s)
    ltac:(destruct s; vm_compute; lia).
