(** Initial-only composition of the actual 64-bit and uint32-array writers.
    The array reloads are protected across the first call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_output_sequence_step C.jet_output_slice.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_uint32_array_init C.jet_write32s_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_write64_then32s_layout m bi input bf base bw edge cursor x xs :
  0 <= input -> input + 4 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  bi <> bf -> bi <> bw -> uint32_array_at m bi input xs ->
  write_frame_at m bf base bw edge cursor (64 + 32 * Z.of_nat (length xs)) ->
  exists mi mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write64)
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mi Vundef /\
    Clight2.eval_funcall ge0 mi (Internal f_write32s)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input);
        Vlong (Int64.repr (Z.of_nat (length xs)))] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor
      (encode (decode_wide W64 (Int64.zero_ext 64 x)) ++ uint32_word_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - (64 + 32 * Z.of_nat (length xs))) /\
    loads_outside_ranges m mi bf (base + 8) (base + 16)
      bw (slice_write_low 64 edge cursor) (write_word_address edge cursor + 8) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - (64 + 32 * Z.of_nat (length xs))) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM Hif Hiw HA HW.
  pose proof HW as [HFBase [HFields [HE [HC [HMax [Hfw [PW HWords]]]]]]].
  assert (HW64 : write_frame_at m bf base bw edge cursor 64).
  { eapply write_frame_at_shorter with (count := 64 + 32 * Z.of_nat (length xs)); [lia|exact HW]. }
  destruct (eval_write_wide_layout W64 m bf base bw edge cursor x HW64)
    as (mi & HWrite & HSlice & HPrefix & HFields64 & HMem64 & HPerm64 & HValid64).
  change (loads_outside_ranges m mi bf (base + 8) (base + 16)
    bw (slice_write_low 64 edge cursor) (write_word_address edge cursor + 8)) in HMem64.
  assert (HFirst : frame_output_cells_at mi bw edge cursor (encode (decode_wide W64 (Int64.zero_ext 64 x)))).
  { apply (wide_output_at_encode W64); [change (64 <= cursor); lia|].
    exists (Int64.zero_ext 64 x); split; [exact HSlice|reflexivity]. }
  assert (HWNext : write_frame_at mi bf base bw edge (cursor - 64) (32 * Z.of_nat (length xs))).
  { eapply write_frame_at_after_slice with (n := 64) (x := Int64.zero_ext 64 x);
      [lia|lia|exact HW|exact HFields64|exact HSlice|exact HMem64|exact HPerm64]. }
  assert (HAI : uint32_array_at mi bi input xs).
  { intros i v Hi. rewrite HMem64 by (left; assumption). exact (HA i v Hi). }
  destruct (eval_write32s_layout mi bi input bf base bw edge (cursor - 64) xs HB HM Hif Hiw HAI HWNext)
    as (mf & HArray & HTail & HPrefixTail & HFieldsTail & HMemTail & HPermTail & HValidTail).
  assert (HfirstFinal : frame_output_cells_at mf bw edge cursor (encode (decode_wide W64 (Int64.zero_ext 64 x)))).
  { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
      (cursor := cursor - 64); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HFirst].
    rewrite (encode_word_length (wide_log W64) (decode_wide W64 (Int64.zero_ext 64 x))).
    change (0 <= cursor - 64 <= cursor - 64); lia. }
  assert (HLo : edge + 8 * ((cursor - (64 + 32 * Z.of_nat (length xs))) / 64) <= slice_write_low 64 edge cursor).
  { pose proof (slice_write_low_bound 64 edge cursor ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (cursor - (64 + 32 * Z.of_nat (length xs))) (cursor - 64) 64
      ltac:(lia) ltac:(lia)). lia. }
  assert (HPrev : write_word_address edge (cursor - 64) <= write_word_address edge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - 64 - 1) (cursor - 1) 64
      ltac:(lia) ltac:(lia)); lia. }
  exists mi, mf. split; [exact HWrite|]. split; [exact HArray|]. split.
  - apply frame_output_cells_at_app. split; [exact HfirstFinal|].
    rewrite (encode_word_length (wide_log W64) (decode_wide W64 (Int64.zero_ext 64 x))). exact HTail.
  - split.
    + eapply write_prefix_at_chain; [exact Hfw| |exact HPrefix|exact HPrefixTail|exact HMemTail]. lia.
    + split.
      * replace (cursor - (64 + 32 * Z.of_nat (length xs))) with
          (cursor - 64 - 32 * Z.of_nat (length xs)) by ring. exact HFieldsTail.
      * split; [exact HMem64|]. split.
        -- intros chunk b ofs Hbf Hbw. rewrite HMemTail.
           ++ apply HMem64; [exact Hbf|]. destruct Hbw as [Hneq|[Hbefore|Hafter]];
                [left|right; left|right; right]; auto; lia.
           ++ exact Hbf.
           ++ replace (cursor - 64 - 32 * Z.of_nat (length xs)) with
                (cursor - (64 + 32 * Z.of_nat (length xs))) by ring.
              destruct Hbw as [Hneq|[Hbefore|Hafter]];
                [left|right; left|right; right]; auto; lia.
        -- split.
           ++ intros b ofs kind p HP. apply HPermTail, HPerm64; exact HP.
           ++ intros b HV. apply HValidTail, HValid64; exact HV.
Qed.
