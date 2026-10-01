(** Nine complete maj/xor_xor/ch jet calls against canonical Simplicity.
    All three readers, the writer and the frame lifecycle follow from initial
    contracts, including crossings and arbitrary initial output contents. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_output_slice C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_complement_wide_layout C.jet_word_repr C.jet_complement_spec.
Require Import C.jet_ternary_spec C.jet_ternary_wide_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wide_ternary_decode k s (x y z : Ty.tySem (Word (wide_log s))) r t u :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned t = @toZ (WordToZ (wide_log s)) y ->
  Int64.unsigned u = @toZ (WordToZ (wide_log s)) z ->
  decode_wide s (Int64.zero_ext (wide_bits s) (ternary_int64 k r t u)) =
    @ternary_word_spec (wide_log s) k Alg.CoreFunSem (x, (y, z)).
Proof.
  intros Hr Ht Hu. pose proof (wide_bits_bounds s) as Hwidth.
  unfold decode_wide. apply word_fromZ_bits. intros j Hj. rewrite <- wide_bits_pow in Hj.
  change (Int64.testbit (Int64.zero_ext (wide_bits s) (ternary_int64 k r t u)) j =
    Z.testbit (@toZ (WordToZ (wide_log s)) (@ternary_word_spec (wide_log s) k Alg.CoreFunSem (x, (y, z)))) j).
  rewrite Int64.bits_zero_ext by (change Int64.zwordsize with 64; lia).
  rewrite zlt_true by lia. rewrite ternary_int64_bits by lia.
  unfold Int64.testbit. rewrite Hr, Ht, Hu. symmetry. apply ternary_word_spec_bits.
Qed.

Theorem eval_wide_ternary_layout_matches_spec env k s m bd dbase bs sbase bi bw edge outedge
    (x y z : Ty.tySem (Word (wide_log s))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 3 * wide_bits s ->
  frame_input_word_at m bi edge rc x ->
  frame_input_word_at m bi edge (rc + wide_bits s) y ->
  frame_input_word_at m bi edge (rc + 2 * wide_bits s) z ->
  write_frame_at m bd dbase bw outedge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_ternary k s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@ternary_word_spec (wide_log s) k Alg.CoreFunSem (x, (y, z)))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - wide_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - wide_bits s) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput1 Hinput2 Hinput3 Hout.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (wide_bits s) ltac:(lia) Hout)
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
  assert (HInputC3 : frame_input_word_at mc bi edge (rc + 2 * wide_bits s) z).
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
  replace (rc + wide_bits s + wide_bits s) with (rc + 2 * wide_bits s) in HReadFields2 by lia.
  assert (HInputR3 : frame_input_word_at mr2 bi edge (rc + 2 * wide_bits s) z).
  { eapply frame_input_bits_at_preserved; [|exact HInputC3].
    intros ofs w HL. rewrite HReadMem2 by (left; congruence).
    rewrite HReadMem1 by (left; congruence). exact HL. }
  assert (PLC3 : Mem.valid_access mr2 Mint64 bl 8 Writable).
  { destruct PLC2 as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HReadPerm2. apply HP; exact Hrange. }
  destruct (eval_read_wide_word_at s mr2 bl 0 bi edge (rc + 2 * wide_bits s) z HLocalBase ltac:(lia)
    HReadFields2 HInputR3 PLC3 HLi)
    as (mr3 & u & Hread3 & Hu & HReadFields3 & HReadMem3 & HReadPerm3 & HReadValid3).
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
  assert (HOutR : write_frame_at mr3 bd dbase bw outedge cursor (wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write_wide_layout s mr3 bd dbase bw outedge cursor (ternary_int64 k r t u) HOutR)
    as (me & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm3. apply HReadPerm2. apply HReadPerm1.
    eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_ternary_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply (wide_output_at_encode s); [lia|]. eexists. split; [exact Houtput|].
        apply wide_ternary_decode; assumption.
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
           ++ rewrite HReadMem3 by (left; exact Hbl). rewrite HReadMem2 by (left; exact Hbl).
              rewrite HReadMem1 by (left; exact Hbl).
              erewrite Mem.load_storebytes_other; [|exact SC|auto].
              eapply Mem.load_alloc_unchanged; eauto.
           ++ pose proof (slice_write_low_bound (wide_bits s) outedge cursor Hwidth ltac:(lia)).
              destruct Hbw as [Hbw|[Hbw|Hbw]]; [left|right; left|right; right]; auto; lia.
Qed.

Theorem wide_ternary_local_spec k s : jet_local_spec (wide_ternary k s)
  (Ty.Prod (Word (wide_log s)) (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))) (Word (wide_log s))
  (fun xyz => @ternary_word_spec (wide_log s) k Alg.CoreFunSem xyz).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x [y z]] HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in * by (destruct s; reflexivity).
  replace (Z.of_nat (bitSize (Ty.Prod (Word (wide_log s)) (Ty.Prod (Word (wide_log s)) (Word (wide_log s))))))
    with (3 * wide_bits s) in Hmax by (destruct s; reflexivity).
  apply frame_input_word_triple_encode in Hin. rewrite <- wide_bits_pow in Hin.
  destruct Hin as [Hin1 [Hin2 Hin3]]. eapply eval_wide_ternary_layout_matches_spec; eauto; lia.
Qed.

Corollary maj16_local_spec : jet_local_spec f_simplicity_maj_16 (Ty.Prod (Word 4) (Ty.Prod (Word 4) (Word 4))) (Word 4)
  (fun xyz => @ternary_word_spec 4 TMaj Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TMaj W16). Qed.
Corollary maj32_local_spec : jet_local_spec f_simplicity_maj_32 (Ty.Prod (Word 5) (Ty.Prod (Word 5) (Word 5))) (Word 5)
  (fun xyz => @ternary_word_spec 5 TMaj Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TMaj W32). Qed.
Corollary maj64_local_spec : jet_local_spec f_simplicity_maj_64 (Ty.Prod (Word 6) (Ty.Prod (Word 6) (Word 6))) (Word 6)
  (fun xyz => @ternary_word_spec 6 TMaj Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TMaj W64). Qed.
Corollary xor_xor16_local_spec : jet_local_spec f_simplicity_xor_xor_16 (Ty.Prod (Word 4) (Ty.Prod (Word 4) (Word 4))) (Word 4)
  (fun xyz => @ternary_word_spec 4 TXorXor Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TXorXor W16). Qed.
Corollary xor_xor32_local_spec : jet_local_spec f_simplicity_xor_xor_32 (Ty.Prod (Word 5) (Ty.Prod (Word 5) (Word 5))) (Word 5)
  (fun xyz => @ternary_word_spec 5 TXorXor Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TXorXor W32). Qed.
Corollary xor_xor64_local_spec : jet_local_spec f_simplicity_xor_xor_64 (Ty.Prod (Word 6) (Ty.Prod (Word 6) (Word 6))) (Word 6)
  (fun xyz => @ternary_word_spec 6 TXorXor Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TXorXor W64). Qed.
Corollary ch16_local_spec : jet_local_spec f_simplicity_ch_16 (Ty.Prod (Word 4) (Ty.Prod (Word 4) (Word 4))) (Word 4)
  (fun xyz => @ternary_word_spec 4 TCh Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TCh W16). Qed.
Corollary ch32_local_spec : jet_local_spec f_simplicity_ch_32 (Ty.Prod (Word 5) (Ty.Prod (Word 5) (Word 5))) (Word 5)
  (fun xyz => @ternary_word_spec 5 TCh Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TCh W32). Qed.
Corollary ch64_local_spec : jet_local_spec f_simplicity_ch_64 (Ty.Prod (Word 6) (Ty.Prod (Word 6) (Word 6))) (Word 6)
  (fun xyz => @ternary_word_spec 6 TCh Alg.CoreFunSem xyz).
Proof. exact (wide_ternary_local_spec TCh W64). Qed.

Theorem wide_ternary_context k s : jet_context_for (wide_ternary k s) (@ternary_word_spec (wide_log s) k).
Proof.
  exact (jet_context _ _ (ternary_word_spec_parametric (wide_log s) k) (wide_ternary_local_spec k s)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_ternary_guarantees k s := jet_local_spec_guarantees _ _ _ _ (wide_ternary_local_spec k s).
Definition wide_ternary_context_guarantees k s :=
  jet_context_guarantees _ _ (ternary_word_spec_parametric (wide_log s) k) (wide_ternary_local_spec k s)
    ltac:(destruct s; vm_compute; lia).
