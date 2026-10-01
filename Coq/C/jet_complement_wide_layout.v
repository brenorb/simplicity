(** Complete complement_16/32/64 implementation-to-Simplicity calls.
    The exact reader value, all writes, and local cleanup are derived from
    the initial memory. Crossing cursors and arbitrary output bits are allowed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_output_slice C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Require Import C.jet_read16_input_word C.jet_read32_input_word_total C.jet_read64_input_word_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_constant_layout C.jet_complement_spec C.jet_complement_wide_exec.
Require Import C.jet_word_repr.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma eval_read_wide_word_at s m bf base bi edge rc (x : Ty.tySem (Word (wide_log s))) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - wide_bits s ->
  frame_fields_at m bf base bi edge rc -> frame_input_word_at m bi edge rc x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists mr r,
    Clight2.eval_funcall ge0 m (Internal (wide_reader s)) [Vptr bf (Ptrofs.repr base)] E0 mr (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ (wide_log s)) x /\
    frame_fields_at mr bf base bi edge (rc + wide_bits s) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mr b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mr b).
Proof. destruct s; [apply eval_read16_word_at|apply eval_read32_word_at|apply eval_read64_word_at]. Qed.

Lemma wide_input_first_load s m bi edge rc (x : Ty.tySem (Word (wide_log s))) :
  frame_input_word_at m bi edge rc x ->
  exists w, Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong w).
Proof.
  intros Hinput.
  pose proof (Hinput 0%nat _ (frame_input_word_bits_nth x 0 ltac:(destruct s; cbn; lia))) as Hbit.
  replace (rc + Z.of_nat 0) with rc in Hbit by lia.
  destruct Hbit as [_ [_ [w [HL _]]]]. exists w; exact HL.
Qed.

Lemma wide_complement_decode s (x : Ty.tySem (Word (wide_log s))) r :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  decode_wide s (Int64.zero_ext (wide_bits s) (Int64.not r)) =
    @complement_spec (wide_log s) Alg.CoreFunSem x.
Proof.
  intros Hr. pose proof (wide_bits_bounds s) as Hwidth.
  unfold decode_wide. apply word_fromZ_bits. intros j Hj.
  rewrite <- wide_bits_pow in Hj.
  change (Int64.testbit (Int64.zero_ext (wide_bits s) (Int64.not r)) j =
    Z.testbit (@toZ (WordToZ (wide_log s)) (@complement_spec (wide_log s) Alg.CoreFunSem x)) j).
  rewrite Int64.bits_zero_ext by (change Int64.zwordsize with 64; lia).
  rewrite zlt_true by lia. rewrite Int64.bits_not by (change Int64.zwordsize with 64; lia).
  unfold Int64.testbit. rewrite Hr. symmetry. apply complement_spec_bits.
  rewrite <- word_width_power, <- wide_bits_pow. exact Hj.
Qed.

Theorem eval_wide_complement_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge
    (x : Ty.tySem (Word (wide_log s))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - wide_bits s -> frame_input_word_at m bi edge rc x ->
  write_frame_at m bd dbase bw outedge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_complement s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@complement_spec (wide_log s) Alg.CoreFunSem x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - wide_bits s) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - wide_bits s) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hinput Hout.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (wide_bits s) ltac:(lia) Hout)
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
  assert (HOutR : write_frame_at mr bd dbase bw outedge cursor (wide_bits s)).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write_wide_layout s mr bd dbase bw outedge cursor (Int64.not r) HOutR)
    as (me & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_wide_complement_composes; eauto.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply (wide_output_at_encode s); [lia|]. eexists. split; [exact Houtput|].
        apply wide_complement_decode; exact Hr.
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
           ++ pose proof (slice_write_low_bound (wide_bits s) outedge cursor Hwidth ltac:(lia)).
              destruct Hbw as [Hbw|[Hbw|Hbw]]; [left|right; left|right; right]; auto; lia.
Qed.

Theorem wide_complement_local_spec s :
  jet_local_spec (wide_complement s) (Word (wide_log s)) (Word (wide_log s))
    (fun x => @complement_spec (wide_log s) Alg.CoreFunSem x).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in * by (destruct s; reflexivity).
  apply frame_input_word_at_encode in Hin.
  exact (eval_wide_complement_layout_matches_spec env s m bd dbase bs sbase bi bw edge outedge x
    cursor rc HB HA HF ltac:(lia) Hin Hout).
Qed.
Corollary complement16_local_spec : jet_local_spec f_simplicity_complement_16 (Word 4) (Word 4)
  (fun x => @complement_spec 4 Alg.CoreFunSem x).
Proof. exact (wide_complement_local_spec W16). Qed.
Corollary complement32_local_spec : jet_local_spec f_simplicity_complement_32 (Word 5) (Word 5)
  (fun x => @complement_spec 5 Alg.CoreFunSem x).
Proof. exact (wide_complement_local_spec W32). Qed.
Corollary complement64_local_spec : jet_local_spec f_simplicity_complement_64 (Word 6) (Word 6)
  (fun x => @complement_spec 6 Alg.CoreFunSem x).
Proof. exact (wide_complement_local_spec W64). Qed.
Theorem wide_complement_context s :
  jet_context_for (wide_complement s) (@complement_spec (wide_log s)).
Proof.
  exact (jet_context _ _ (complement_spec_parametric (wide_log s)) (wide_complement_local_spec s)
    ltac:(destruct s; vm_compute; lia)).
Qed.
Definition wide_complement_guarantees s := jet_local_spec_guarantees _ _ _ _ (wide_complement_local_spec s).
Definition wide_complement_context_guarantees s :=
  jet_context_guarantees _ _ (complement_spec_parametric (wide_log s)) (wide_complement_local_spec s)
    ltac:(destruct s; vm_compute; lia).
