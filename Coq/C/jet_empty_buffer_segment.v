(** Reusable actual false-tag plus skipBits sequence for absent buffer chunks.
    Arbitrary padding contents survive, and writable continuation is derived.
    A complete write_buffer8 loop and enclosing jet remain required. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Memory Events Clight ClightBigstep.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_spec C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_writeBit_layout_total C.jet_skipBits_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma write_frame_at_after_padding m mf bf base bw edge cursor n count :
  0 <= n -> 0 <= count -> write_frame_at m bf base bw edge cursor (n + count) ->
  frame_fields_at mf bf base bw edge (cursor - n) ->
  (forall chunk bb ofs, bb <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
    Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs) ->
  (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) ->
  write_frame_at mf bf base bw edge (cursor - n) count.
Proof.
  intros Hn Hcount [HB [HF [HE [HC [HM [HD [PC HW]]]]]]] HF' HL HP.
  split; [exact HB|]. split; [exact HF'|]. split; [exact HE|]. split; [lia|].
  split; [lia|]. split; [exact HD|]. split.
  - destruct PC as [P A]. split; [|exact A]. intros addr HR. apply HP, P; exact HR.
  - intros i Hi.
    assert (Haddr : write_cell_address edge (cursor - n) i = write_cell_address edge cursor (i + n)).
    { unfold write_cell_address. replace (cursor - n - 1 - i) with (cursor - 1 - (i + n)) by lia; reflexivity. }
    rewrite Haddr. destruct (HW (i + n) ltac:(lia)) as [H0 [HA [PW [v LV]]]].
    split; [exact H0|]. split; [exact HA|]. split.
    + destruct PW as [P A]. split; [|exact A]. intros addr HR. apply HP, P; exact HR.
    + exists v. rewrite HL by auto; exact LV.
Qed.

Theorem eval_empty_buffer_segment m bf base bw edge cursor count tail :
  0 <= tail -> write_frame_at m bf base bw edge cursor (1 + Z.of_nat count + tail) ->
  exists mb mf,
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint Int.zero] E0 mb (Vint Int.zero) /\
    Clight2.eval_funcall ge0 mb (Internal f_skipBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat count))] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (Some Datatypes.false :: repeat None count) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - (1 + Z.of_nat count)) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - (1 + Z.of_nat count)) / 64)) (write_word_address edge cursor + 8) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  intros Htail HFrame. pose proof HFrame as [HB [HF [HE [HC [HM [HD [PD HW]]]]]]].
  assert (Hone : write_frame_at m bf base bw edge cursor 1)
    by (eapply write_frame_at_shorter with (count := 1 + Z.of_nat count + tail); [lia|exact HFrame]).
  destruct (eval_writeBit_layout m bf base bw edge cursor Datatypes.false Hone)
    as (mb & bitword & HBit & HBitLoad & HBitValue & HBitPrefix & HBitFields & HBitMem & HBitPerm & HBitValid).
  assert (Hnext : write_frame_at mb bf base bw edge (cursor - 1) (Z.of_nat count + tail)).
  { eapply write_frame_at_after_bit with (w := bitword); [lia| |exact HBitFields|exact HBitLoad|exact HBitMem|exact HBitPerm].
    replace (Z.of_nat count + tail + 1) with (1 + Z.of_nat count + tail) by lia; exact HFrame. }
  assert (Hpadding : write_frame_at mb bf base bw edge (cursor - 1) (Z.of_nat count))
    by (eapply write_frame_at_shorter with (count := Z.of_nat count + tail); [lia|exact Hnext]).
  destruct (eval_skipBits_padding mb bf base bw edge (cursor - 1) count Hpadding)
    as (mf & HSkip & HCells & HSkipPrefix & HSkipFields & HSkipMem & HSkipPerm & HSkipValid).
  assert (HTail : write_frame_at mf bf base bw edge (cursor - (1 + Z.of_nat count)) tail).
  { replace (cursor - (1 + Z.of_nat count)) with (cursor - 1 - Z.of_nat count) by lia.
    eapply write_frame_at_after_padding; [lia|exact Htail|exact Hnext|exact HSkipFields|exact HSkipMem|exact HSkipPerm]. }
  assert (HFirst : frame_output_cells_at mf bw edge cursor [Some Datatypes.false]).
  { intros [|[|i]] c Hi; cbn in Hi; try discriminate. injection Hi as <-.
    cbn [cell_matches]. split; [lia|]. exists bitword.
    replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. split.
    - change (Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong bitword)).
      rewrite HSkipMem by auto; exact HBitLoad.
    - symmetry; exact HBitValue. }
  exists mb, mf. split; [exact HBit|]. split; [exact HSkip|]. split.
  - change (frame_output_cells_at mf bw edge cursor ([Some Datatypes.false] ++ repeat None count)).
    apply frame_output_cells_at_app. split; [exact HFirst|]. exact HCells.
  - split.
    + eapply write_prefix_at_preserved; [| |exact HBitPrefix].
      * intros ofs v HL; exact HL.
      * intros ofs v HL. rewrite HSkipMem by auto; exact HL.
    + split; [exact HTail|]. split.
      * intros chunk bb ofs Hbf Hbw. rewrite HSkipMem by exact Hbf.
        apply HBitMem; [exact Hbf|].
        assert (HLow : edge + 8 * ((cursor - (1 + Z.of_nat count)) / 64) <= write_word_address edge cursor).
        { unfold write_word_address. pose proof (Z.div_le_mono (cursor - (1 + Z.of_nat count)) (cursor - 1) 64
            ltac:(lia) ltac:(lia)); nia. }
        destruct Hbw as [N|[L|R]]; [left; exact N|right; left; lia|right; right; exact R].
      * split.
        -- intros bb ofs kind p H. apply HSkipPerm, HBitPerm; exact H.
        -- intros bb H. apply HSkipValid, HBitValid; exact H.
Qed.
