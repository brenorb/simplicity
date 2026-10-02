(** Both output branches of parse_sequence, derived from an arbitrary writable
    18-cell frame.  This executes helpers, not yet the enclosing jet call. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_spec.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_output_layout_step C.jet_writeBit_layout_total.
Require Import C.jet_carry_wide_layout C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_parse_sequence_spec C.jet_parse_sequence_exec C.jet_skipBits_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_parse_sequence_writer m bf base bw edge cursor r :
  write_frame_at m bf base bw edge cursor 18 ->
  exists mb mf,
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if parse_sequence_enabled r then Int.one else Int.zero)]
      E0 mb (Vint (if parse_sequence_enabled r then Int.one else Int.zero)) /\
    parse_sequence_branch_calls mb mf bf (Ptrofs.repr base) r /\
    frame_output_cells_at mf bw edge cursor (@encode (Ty.Sum Ty.Unit (Ty.Sum (Word 4) (Word 4)))
      (if parse_sequence_enabled r then
        inr (if parse_sequence_tag r then inr (decode_wide W16
          (Int64.zero_ext 16 (parse_sequence_payload r))) else inl (decode_wide W16
          (Int64.zero_ext 16 (parse_sequence_payload r))))
       else @inl unit (Ty.tySem (Ty.Sum (Word 4) (Word 4))) tt)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 18) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 18) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame. pose proof HFrame as [HB [HF [HE [HC [HM [HD [PD HW]]]]]]].
  pose proof (write_layout_index cursor ltac:(lia)) as [_ [HK _]].
  assert (HFrame1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter with (count := 18); [lia|exact HFrame]. }
  destruct (eval_writeBit_layout m bf base bw edge cursor (parse_sequence_enabled r) HFrame1)
    as [mb [bithigh [HBit [HBitLoad [HBitValue [HPrefix1
      [HFields1 [HMem1 [HPerm1 HValid1]]]]]]]]].
  assert (HFrameTail : write_frame_at mb bf base bw edge (cursor - 1) 17).
  { eapply write_frame_at_after_bit with (w := bithigh); eauto; lia. }
  assert (HTail : exists mf,
    parse_sequence_branch_calls mb mf bf (Ptrofs.repr base) r /\
    frame_output_cells_at mf bw edge (cursor - 1)
      (if parse_sequence_enabled r then Some (parse_sequence_tag r) ::
        encode (decode_wide W16 (Int64.zero_ext 16 (parse_sequence_payload r)))
       else repeat None 17) /\
    write_prefix_at mb mf bw edge (cursor - 1) /\
    frame_fields_at mf bf base bw edge (cursor - 18) /\
    loads_outside_ranges mb mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 18) / 64)) (write_word_address edge (cursor - 1) + 8) /\
    (forall b ofs kind p, Mem.perm mb b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block mb b -> Mem.valid_block mf b)).
  { unfold parse_sequence_branch_calls. destruct (parse_sequence_enabled r) eqn:Hen.
    - destruct (eval_carry_wide_layout W16 mb bf base bw edge (cursor - 1)
        (parse_sequence_tag r) (parse_sequence_payload r) HFrameTail)
        as [mt [mf [Htag [Hwrite [Hvalue [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]]]].
      exists mf. split; [exists mt; auto|]. split.
      + apply (carry_wide_output_encode W16) in Hvalue; [|change (17 <= cursor - 1); lia].
        destruct (parse_sequence_tag r); exact Hvalue.
      + split; [exact Hprefix|]. split.
        * replace (cursor - 18) with (cursor - 1 - (1 + wide_bits W16))
            by (cbn [wide_bits]; lia).
          exact Hfields.
        * split.
          -- intros chunk b ofs Hbf Hbw. apply Hmem; [exact Hbf|].
             assert (Hlow : edge + 8 * ((cursor - 18) / 64) <=
               slice_write_low 16 edge (cursor - 1 - 1)).
             { replace (cursor - 18) with (cursor - 1 - 1 - 16) by lia.
               apply slice_write_low_bound; lia. }
             destruct Hbw as [Hneq|[Hbefore|Hafter]];
               [left|right; left|right; right]; auto; change (wide_bits W16) with 16; lia.
          -- split; assumption.
    - destruct (eval_skipBits_padding mb bf base bw edge (cursor - 1) 17 HFrameTail)
        as [mf [Hskip [Hcells [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]].
      exists mf. split; [exact Hskip|]. split; [exact Hcells|].
      split; [exact Hprefix|]. split.
      + replace (cursor - 18) with (cursor - 1 - Z.of_nat 17) by lia. exact Hfields.
      + split; [intros chunk b ofs Hbf Hbw; apply Hmem; exact Hbf|]. split; assumption. }
  destruct HTail as [mf [Hbranch [Htail [HPrefixTail [HFieldsTail [HMemTail [HPermTail HValidTail]]]]]]].
  assert (HHead : exists w,
    Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) /\
    word_outside_eq 0 (write_word_shift cursor - 1) w bithigh).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [Hshift Haddr].
      exists bithigh. split.
      + rewrite HMemTail; [exact HBitLoad|left; congruence|right; right].
        rewrite Haddr. change (write_word_address edge cursor - 8 + 8 <=
          write_word_address edge cursor). lia.
      + intros i Hi Hout; reflexivity.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [Hshift Haddr].
      unfold write_prefix_at in HPrefixTail. rewrite Hshift, Haddr in HPrefixTail.
      exact (HPrefixTail bithigh HBitLoad). }
  destruct HHead as [outputhigh [HHigh HSame]].
  assert (HPrev : write_word_address edge (cursor - 1) <= write_word_address edge cursor).
  { destruct (Z.eq_dec (write_word_shift cursor) 1) as [Hboundary|Hinside].
    - destruct (write_layout_previous_boundary edge cursor Hboundary) as [_ Haddr]. lia.
    - destruct (write_layout_previous_inside edge cursor ltac:(lia)) as [_ Haddr]. lia. }
  assert (HLow : edge + 8 * ((cursor - 18) / 64) <= write_word_address edge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - 18) (cursor - 1) 64
      ltac:(lia) ltac:(lia)). lia. }
  exists mb, mf. split; [exact HBit|]. split; [exact Hbranch|]. split.
  - assert (Hflag : frame_output_cells_at mf bw edge cursor
      [Some (parse_sequence_enabled r)]).
    { intros [|[|i]] c Hi; cbn in Hi; try discriminate. injection Hi as <-.
      cbn [cell_matches]. split; [lia|]. exists outputhigh.
      replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia.
      split; [exact HHigh|]. symmetry. rewrite HSame.
      - exact HBitValue.
      - unfold write_word_shift in HK. lia.
      - right. unfold write_word_shift; lia. }
    destruct (parse_sequence_enabled r) eqn:Hen.
    + rewrite encode_parse_sequence_enabled.
      change (frame_output_cells_at mf bw edge cursor
        ([Some Datatypes.true] ++ Some (parse_sequence_tag r) ::
          encode (decode_wide W16 (Int64.zero_ext 16 (parse_sequence_payload r))))).
      apply frame_output_cells_at_app. split; [exact Hflag|exact Htail].
    + change (frame_output_cells_at mf bw edge cursor ([Some Datatypes.false] ++ repeat None 17)).
      apply frame_output_cells_at_app. split; [exact Hflag|exact Htail].
  - split.
    + intros old HL. destruct (HPrefix1 old HL) as [w [HW' HOld]].
      assert (w = bithigh) by congruence. subst w.
      exists outputhigh. split; [exact HHigh|].
      intros i Hi Hout. rewrite HSame; [apply HOld; assumption|exact Hi|lia].
    + split; [exact HFieldsTail|]. split.
      * intros chunk b ofs Hbf Hbw. rewrite HMemTail; [|exact Hbf|].
        -- apply HMem1; [exact Hbf|].
           destruct Hbw as [Hneq|[Hbefore|Hafter]];
             [left|right; left|right; right]; auto; lia.
        -- destruct Hbw as [Hneq|[Hbefore|Hafter]];
             [left|right; left|right; right]; auto; lia.
      * split.
        -- intros b ofs kind p HP. apply HPermTail, HPerm1; exact HP.
        -- intros b HV. apply HValidTail, HValid1; exact HV.
Qed.
