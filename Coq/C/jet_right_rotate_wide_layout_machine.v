(** Initial-only execution and memory observations for right_rotate_32/64.
    This machine-value result is internal; coverage requires its bridge to
    the canonical variable-control Simplicity rotation program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_frame_spec C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_output_slice C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_constant_layout C.jet_word_repr.
Require Import C.jet_complement_wide_layout C.jet_read8_wide_sequence C.jet_left_rotate_wide_exec C.jet_right_rotate_wide_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_rotate_byte_machine_value s (amount : Ty.tySem (Word 3))
    (x : Ty.tySem (Word (wide_log (byte_rotate_width s)))) :=
  decode_wide (byte_rotate_width s) (Int64.zero_ext (wide_bits (byte_rotate_width s))
    (right_rotate_byte_payload s (Int64.repr (@toZ (WordToZ (wide_log (byte_rotate_width s))) x))
      (Int.repr (@toZ (WordToZ 3) amount)))).

Theorem eval_right_rotate_byte_layout_machine env s m bd dbase bs sbase bi bw edge outedge
    (amount : Ty.tySem (Word 3)) (x : Ty.tySem (Word (wide_log (byte_rotate_width s)))) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - (8 + wide_bits (byte_rotate_width s)) -> frame_input_word_at m bi edge rc amount -> frame_input_word_at m bi edge (rc + 8) x ->
  write_frame_at m bd dbase bw outedge cursor (wide_bits (byte_rotate_width s)) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (right_rotate_byte_function s))
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (right_rotate_byte_machine_value s amount x)) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - wide_bits (byte_rotate_width s)) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - wide_bits (byte_rotate_width s)) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSbase HSAlign [HSE HSO] HRC Hamount Hinput Hout.
  pose proof (wide_bits_bounds (byte_rotate_width s)) as Hwidth.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [HD [PD HW]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (wide_bits (byte_rotate_width s)) ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLi : bl <> bi).
  { destruct (wide_input_first_load (byte_rotate_width s) m bi edge (rc + 8) x Hinput) as [w HL].
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
  assert (HInputC : frame_input_word_at mc bi edge (rc + 8) x).
  { eapply frame_input_bits_at_preserved; [|exact Hinput].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HAmountC : frame_input_word_at mc bi edge rc amount).
  { eapply frame_input_bits_at_preserved; [|exact Hamount].
    intros ofs w HL. erewrite Mem.load_storebytes_other;
      [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
  destruct (eval_read8_wide_sequence (byte_rotate_width s) mc bl 0 bi edge rc amount x
    HLocalBase HRC (conj HLE HLO) HAmountC HInputC PLC HLi)
    as (mr & mr2 & a & r & Hread8 & HamountValue & HamountCast & Hread & Hr &
      HReadFields & HReadMem & HReadPerm & HReadValid).
  assert (HBeforeLoad : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr2 b ofs = Some v).
  { intros chunk b ofs v Hb HL. rewrite HReadMem by (left; destruct Hb; subst; congruence).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|].
    destruct Hb; subst; auto. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr2 b ofs kind p).
  { intros b ofs kind p HP. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; eauto. }
  assert (HOutR : write_frame_at mr2 bd dbase bw outedge cursor (wide_bits (byte_rotate_width s))).
  { eapply write_frame_at_preserved; eauto. }
  destruct (eval_write_wide_layout (byte_rotate_width s) mr2 bd dbase bw outedge cursor (right_rotate_byte_payload s r a) HOutR)
    as (me & Hwrite & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. apply HReadPerm. eapply Mem.perm_storebytes_1; [exact SC|].
    apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply eval_right_rotate_byte_composes; eauto.
    rewrite HamountValue. apply word_toZ_range.
  - split.
    + eapply frame_output_cells_preserved.
      * intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * apply (wide_output_at_encode (byte_rotate_width s)); [lia|]. eexists. split; [exact Houtput|].
        unfold right_rotate_byte_machine_value.
        replace a with (Int.repr (@toZ (WordToZ 3) amount)) by
          (rewrite <- HamountValue; apply Int.repr_unsigned).
        replace r with (Int64.repr (@toZ (WordToZ (wide_log (byte_rotate_width s))) x)) by
          (rewrite <- Hr; apply Int64.repr_unsigned).
        reflexivity.
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
           ++ pose proof (slice_write_low_bound (wide_bits (byte_rotate_width s)) outedge cursor Hwidth ltac:(lia)).
              destruct Hbw as [Hbw|[Hbw|Hbw]]; [left|right; left|right; right]; auto; lia.
Qed.

