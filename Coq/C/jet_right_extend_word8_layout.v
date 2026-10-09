(** Complete right_extend_8_{16,32,64} calls against literal canonical programs.
    Every writer-run, allocation/copy/read/free and memory premise is discharged
    from initial frames, without output initialization or cursor restrictions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_read8 C.jet_frame_spec.
Require Import C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_write8_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_extend_word8_exec C.jet_right_extend_word8_exec C.jet_extend_word8_loop.
Require Import C.jet_extend_word_spec C.jet_right_extend_word_spec C.jet_right_extend_word8_loop C.jet_write8_sequence C.jet_add8_word C.jet_add8.
Require Import C.jet_word_repr.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_right_extend_word8_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem Word8) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  byte_slice_at m bi edge rc x -> write_frame_at m bd dbase bw outedge cursor (extend_word8_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (right_extend_word8_function s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@right_extend_word_spec 3 (extend_word8_depth s) Alg.CoreFunSem x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - extend_word8_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - extend_word8_bits s) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] Hinput Hout.
  assert (Hwidth : 8 <= extend_word8_bits s) by (destruct s; cbn; lia).
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (extend_word8_bits s) ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct Hinput as [_ [_ [h [l [HL _]]]]]. eapply fresh_frame_not_loaded; eauto. }
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
  assert (HInputC : byte_slice_at mc bi edge rc x).
  { eapply byte_slice_preserved; [|exact Hinput].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_read8_byte_at mc bl 0 bi edge rc x HLocalBase (conj HLE HLO) HInputC PLC HLi)
    as (mr & payload & Hread & Hdecode & HReadFields & HReadMem & HReadPerm & HReadValid).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v Hb HL. rewrite HReadMem by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr bd dbase bw outedge cursor (extend_word8_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  assert (HOutSequence : write_frame_at mr bd dbase bw outedge cursor
    (8 * Z.of_nat (length (right_extend_word8_output_args s (read8_result payload))))).
  { rewrite right_extend_word8_args_length; exact HOutR. }
  destruct (write8_sequence_run_layout mr bd dbase bw outedge cursor
    (right_extend_word8_output_args s (read8_result payload)) HOutSequence)
    as (me & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  rewrite right_extend_word8_args_length in Hfields, Hmemory.
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_right_extend_word8_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * rewrite (right_extend_word8_sequence_denotes s x (read8_result payload)) in Houtput.
        -- exact Houtput.
        -- change (Int.unsigned (add8_u (read8_result payload)) = @toZ (WordToZ 3) x).
           rewrite read8_result_unsigned, Hdecode; reflexivity.
        -- apply (toZ_injective (WordToZ 3)).
           rewrite decode_word8_of_int.
           change (Int.unsigned (add8_u (read8_result payload)) mod 256 = @toZ (WordToZ 3) x).
           rewrite read8_result_unsigned, Hdecode.
           pose proof (word_toZ_range 3 x). rewrite Z.mod_small; [reflexivity|exact H].
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
           rewrite Hmemory; [|exact Hbd|].
           ++ rewrite HReadMem by (left; exact Hbl).
              erewrite Mem.load_storebytes_other; [|exact SC|auto].
              eapply Mem.load_alloc_unchanged; eauto.
           ++ exact Hbw.
Qed.

Theorem right_extend_word8_local_spec s : jet_local_spec (right_extend_word8_function s)
  Word8 (Vector Word8 (extend_word8_depth s))
  (fun x => @right_extend_word_spec 3 (extend_word8_depth s) Alg.CoreFunSem x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Word8)) with 8 in Hmax.
  replace (Z.of_nat (bitSize (Vector Word8 (extend_word8_depth s))))
    with (extend_word8_bits s) in Hout |- * by (destruct s; reflexivity).
  eapply eval_right_extend_word8_layout_matches_spec; eauto.
  apply byte_slice_at_encode. split; [lia|exact Hin].
Qed.
Corollary right_extend_8_16_local_spec : jet_local_spec f_simplicity_right_extend_8_16 Word8 (Word 4)
  (fun x => @right_extend_word_spec 3 1 Alg.CoreFunSem x).
Proof. exact (right_extend_word8_local_spec E8to16). Qed.
Corollary right_extend_8_32_local_spec : jet_local_spec f_simplicity_right_extend_8_32 Word8 (Word 5)
  (fun x => @right_extend_word_spec 3 2 Alg.CoreFunSem x).
Proof. exact (right_extend_word8_local_spec E8to32). Qed.
Corollary right_extend_8_64_local_spec : jet_local_spec f_simplicity_right_extend_8_64 Word8 (Word 6)
  (fun x => @right_extend_word_spec 3 3 Alg.CoreFunSem x).
Proof. exact (right_extend_word8_local_spec E8to64). Qed.

Theorem right_extend_word8_context s : jet_context_for (right_extend_word8_function s)
  (fun term => @right_extend_word_spec 3 (extend_word8_depth s) term).
Proof.
  exact (jet_context _ _ (right_extend_word_spec_parametric 3 (extend_word8_depth s))
    (right_extend_word8_local_spec s) ltac:(destruct s; vm_compute; lia)).
Qed.
Definition right_extend_word8_guarantees s := jet_local_spec_guarantees _ _ _ _ (right_extend_word8_local_spec s).
Definition right_extend_word8_context_guarantees s :=
  jet_context_guarantees _ _ (right_extend_word_spec_parametric 3 (extend_word8_depth s))
    (right_extend_word8_local_spec s) ltac:(destruct s; vm_compute; lia).
