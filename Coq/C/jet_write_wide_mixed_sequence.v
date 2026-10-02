(** Initial-only sequencing of actual wide writers with varying widths.
    In particular, DivMod128_64 writes 32, 32 and 64 bits, not two 64-bit calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_layout_step C.jet_output_sequence_step C.jet_output_slice.
Require Import C.jet_encoding C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint wide_mixed_bits (xs : list (wide_size * int64)) : Z :=
  match xs with [] => 0 | (s,_) :: xs => wide_bits s + wide_mixed_bits xs end.
Fixpoint write_wide_mixed_run bf base (xs : list (wide_size * int64)) m mf : Prop :=
  match xs with
  | [] => m = mf
  | (s,x) :: xs => exists mi,
    Clight2.eval_funcall ge0 m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mi Vundef /\
    write_wide_mixed_run bf base xs mi mf
  end.
Definition wide_mixed_cells (xs : list (wide_size * int64)) :=
  concat (map (fun sx => encode (decode_wide (fst sx) (Int64.zero_ext (wide_bits (fst sx)) (snd sx)))) xs).

Lemma wide_mixed_bits_nonnegative xs : 0 <= wide_mixed_bits xs.
Proof.
  induction xs as [|[s x] xs IH]; cbn [wide_mixed_bits]; [lia|].
  pose proof (wide_bits_bounds s); lia.
Qed.

Theorem write_wide_mixed_run_layout m bf base bw edge cursor xs :
  write_frame_at m bf base bw edge cursor (wide_mixed_bits xs) ->
  exists mf,
    write_wide_mixed_run bf base xs m mf /\
    frame_output_cells_at mf bw edge cursor (wide_mixed_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - wide_mixed_bits xs) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - wide_mixed_bits xs) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m cursor. induction xs as [|[s x] xs IH]; intros m cursor HW.
  - exists m. split; [reflexivity|]. split.
    + intros i c Hi. destruct i; discriminate.
    + split.
      * intros old HL. exists old. split; [exact HL|].
        unfold word_outside_eq; intros; reflexivity.
      * split.
        -- change (frame_fields_at m bf base bw edge (cursor - 0)).
           rewrite Z.sub_0_r. exact (proj1 (proj2 HW)).
        -- split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
  - pose proof (wide_bits_bounds s) as Hwidth.
    pose proof (wide_mixed_bits_nonnegative xs) as HtailBits.
    pose proof HW as [HFBase [HFields [HE [HC [HMax [Hfw [PW HWords]]]]]]].
    assert (HWHead : write_frame_at m bf base bw edge cursor (wide_bits s)).
    { eapply write_frame_at_shorter with (count := wide_mixed_bits ((s,x) :: xs));
        [cbn [wide_mixed_bits]; lia|exact HW]. }
    destruct (eval_write_wide_layout s m bf base bw edge cursor x HWHead)
      as [mi [Hwrite [Hslice [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]].
    assert (HFirst : frame_output_cells_at mi bw edge cursor
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)))).
    { apply (wide_output_at_encode s); [cbn [wide_mixed_bits] in HC; lia|].
      exists (Int64.zero_ext (wide_bits s) x); split; [exact Hslice|reflexivity]. }
    assert (HWNext : write_frame_at mi bf base bw edge (cursor - wide_bits s) (wide_mixed_bits xs)).
    { eapply write_frame_at_after_slice with (n := wide_bits s) (x := Int64.zero_ext (wide_bits s) x);
        [lia|lia|exact HW|exact Hfields|exact Hslice|exact Hmem|exact Hperm]. }
    destruct (IH mi (cursor - wide_bits s) HWNext)
      as [mf [Hrun [Htail [HPrefixTail [HFieldsTail [HMemTail [HPermTail HValidTail]]]]]]].
    assert (HfirstFinal : frame_output_cells_at mf bw edge cursor
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)))).
    { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
        (cursor := cursor - wide_bits s); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HFirst].
      rewrite (encode_word_length (wide_log s) (decode_wide s (Int64.zero_ext (wide_bits s) x))), <- wide_bits_pow.
      change (0 <= cursor - wide_bits s <= cursor - wide_bits s).
      cbn [wide_mixed_bits] in HC; lia. }
    assert (HLo : edge + 8 * ((cursor - wide_mixed_bits ((s,x) :: xs)) / 64) <=
      slice_write_low (wide_bits s) edge cursor).
    { pose proof (slice_write_low_bound (wide_bits s) edge cursor ltac:(lia)
        ltac:(cbn [wide_mixed_bits] in HC; lia)) as HL.
      pose proof (Z.div_le_mono (cursor - wide_mixed_bits ((s,x) :: xs)) (cursor - wide_bits s) 64
        ltac:(lia) ltac:(cbn [wide_mixed_bits]; lia)). nia. }
    assert (HPrev : write_word_address edge (cursor - wide_bits s) <= write_word_address edge cursor).
    { unfold write_word_address. pose proof (Z.div_le_mono (cursor - wide_bits s - 1) (cursor - 1) 64
        ltac:(lia) ltac:(lia)); nia. }
    exists mf. split; [exists mi; auto|]. split.
    + change (frame_output_cells_at mf bw edge cursor
        (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)) ++ wide_mixed_cells xs)).
      apply frame_output_cells_at_app. split; [exact HfirstFinal|].
      rewrite (encode_word_length (wide_log s) (decode_wide s (Int64.zero_ext (wide_bits s) x))), <- wide_bits_pow.
      exact Htail.
    + split.
      * eapply write_prefix_at_chain; [exact Hfw| |exact Hprefix|exact HPrefixTail|exact HMemTail].
        cbn [wide_mixed_bits] in HC; lia.
      * split.
        -- change (frame_fields_at mf bf base bw edge (cursor - (wide_bits s + wide_mixed_bits xs))).
           replace (cursor - (wide_bits s + wide_mixed_bits xs)) with
             (cursor - wide_bits s - wide_mixed_bits xs) by ring. exact HFieldsTail.
        -- split.
           ++ intros chunk b ofs Hbf Hbw. rewrite HMemTail.
              ** apply Hmem; [exact Hbf|]. destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto.
                 change (ofs + size_chunk chunk <= slice_write_low (wide_bits s) edge cursor). nia.
              ** exact Hbf.
              ** replace (cursor - wide_bits s - wide_mixed_bits xs) with
                   (cursor - wide_mixed_bits ((s,x) :: xs)) by (cbn [wide_mixed_bits]; ring).
                 destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto; nia.
           ++ split.
              ** intros b ofs kind p HP. apply HPermTail, Hperm; exact HP.
              ** intros b HV. apply HValidTail, Hvalid; exact HV.
Qed.
