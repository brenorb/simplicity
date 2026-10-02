(** Initial-only sequencing of actual wide writers, shared across widths.
    All run premises are derived; existing output and unrelated memory remain
    framed across arbitrary valid cursors and crossings. *)
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

Fixpoint write_wide_sequence_run s bf base (xs : list int64) m mf : Prop :=
  match xs with
  | [] => m = mf
  | x :: xs => exists mi,
    Clight2.eval_funcall ge0 m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mi Vundef /\
    write_wide_sequence_run s bf base xs mi mf
  end.
Definition wide_sequence_cells s (xs : list int64) :=
  concat (map (fun x => encode (decode_wide s (Int64.zero_ext (wide_bits s) x))) xs).

Theorem write_wide_sequence_run_layout s m bf base bw edge cursor xs :
  write_frame_at m bf base bw edge cursor (wide_bits s * Z.of_nat (length xs)) ->
  exists mf,
    write_wide_sequence_run s bf base xs m mf /\
    frame_output_cells_at mf bw edge cursor (wide_sequence_cells s xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - wide_bits s * Z.of_nat (length xs)) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - wide_bits s * Z.of_nat (length xs)) / 64))
        (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  pose proof (wide_bits_bounds s) as Hwidth.
  revert m cursor. induction xs as [|x xs IH]; intros m cursor HW.
  - exists m. split; [reflexivity|]. split.
    + intros i c Hi. destruct i; discriminate.
    + split.
      * intros old HL. exists old. split; [exact HL|].
        unfold word_outside_eq; intros; reflexivity.
      * split.
        -- change (frame_fields_at m bf base bw edge (cursor - wide_bits s * 0)).
           rewrite Z.mul_0_r, Z.sub_0_r. exact (proj1 (proj2 HW)).
        -- split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
  - pose proof HW as [HFBase [HFields [HE [HC [HMax [Hfw [PW HWords]]]]]]].
    assert (HW8 : write_frame_at m bf base bw edge cursor (wide_bits s)).
    { eapply write_frame_at_shorter with (count := wide_bits s * Z.of_nat (length (x :: xs)));
        [cbn [length]; nia|exact HW]. }
    destruct (eval_write_wide_layout s m bf base bw edge cursor x HW8)
      as [mi [Hwrite [Hslice [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]].
    assert (HFirst : frame_output_cells_at mi bw edge cursor
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)))).
    { apply (wide_output_at_encode s); [cbn [length] in HC; nia|].
      exists (Int64.zero_ext (wide_bits s) x); split; [exact Hslice|reflexivity]. }
    assert (HWNext : write_frame_at mi bf base bw edge (cursor - wide_bits s) (wide_bits s * Z.of_nat (length xs))).
    { eapply write_frame_at_after_slice with (n := wide_bits s) (x := Int64.zero_ext (wide_bits s) x);
        [nia|nia| |exact Hfields|exact Hslice|exact Hmem|exact Hperm].
      replace (wide_bits s + wide_bits s * Z.of_nat (length xs)) with (wide_bits s * Z.of_nat (length (x :: xs)))
        by (cbn [length]; nia). exact HW. }
    destruct (IH mi (cursor - wide_bits s) HWNext)
      as [mf [Hrun [Htail [HPrefixTail [HFieldsTail [HMemTail [HPermTail HValidTail]]]]]]].
    assert (HfirstFinal : frame_output_cells_at mf bw edge cursor
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)))).
    { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
        (cursor := cursor - wide_bits s); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HFirst].
      rewrite (encode_word_length (wide_log s) (decode_wide s (Int64.zero_ext (wide_bits s) x))), <- wide_bits_pow.
      change (0 <= cursor - wide_bits s <= cursor - wide_bits s).
      cbn [length] in HC; nia. }
    assert (HLo : edge + 8 * ((cursor - wide_bits s * Z.of_nat (length (x :: xs))) / 64) <=
      slice_write_low (wide_bits s) edge cursor).
    { pose proof (slice_write_low_bound (wide_bits s) edge cursor ltac:(nia) ltac:(cbn [length] in HC; nia)) as HL.
      pose proof (Z.div_le_mono (cursor - wide_bits s * Z.of_nat (length (x :: xs))) (cursor - wide_bits s) 64
        ltac:(nia) ltac:(cbn [length]; nia)). nia. }
    assert (HPrev : write_word_address edge (cursor - wide_bits s) <= write_word_address edge cursor).
    { unfold write_word_address. pose proof (Z.div_le_mono (cursor - wide_bits s - 1) (cursor - 1) 64
        ltac:(nia) ltac:(nia)); nia. }
    exists mf. split; [exists mi; auto|]. split.
    + change (frame_output_cells_at mf bw edge cursor
        (encode (decode_wide s (Int64.zero_ext (wide_bits s) x)) ++ wide_sequence_cells s xs)).
      apply frame_output_cells_at_app. split; [exact HfirstFinal|].
      rewrite (encode_word_length (wide_log s) (decode_wide s (Int64.zero_ext (wide_bits s) x))), <- wide_bits_pow.
      exact Htail.
    + split.
      * eapply write_prefix_at_chain; [exact Hfw| |exact Hprefix|exact HPrefixTail|exact HMemTail].
        cbn [length] in HC; nia.
      * split.
        -- replace (cursor - wide_bits s * Z.of_nat (length (x :: xs))) with
             (cursor - wide_bits s - wide_bits s * Z.of_nat (length xs)) by (cbn [length]; nia). exact HFieldsTail.
        -- split.
           ++ intros chunk b ofs Hbf Hbw. rewrite HMemTail.
              ** apply Hmem; [exact Hbf|]. destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto.
                 change (ofs + size_chunk chunk <= slice_write_low (wide_bits s) edge cursor). nia.
              ** exact Hbf.
              ** replace (cursor - wide_bits s - wide_bits s * Z.of_nat (length xs)) with
                   (cursor - wide_bits s * Z.of_nat (length (x :: xs))) by (cbn [length]; nia).
                 destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto; nia.
           ++ split.
              ** intros b ofs kind p HP. apply HPermTail, Hperm; exact HP.
              ** intros b HV. apply HValidTail, Hvalid; exact HV.
Qed.
