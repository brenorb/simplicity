(** Complete initialized-context writer from initial context/array/frame
    observations. No intermediate calls or reloads are assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_sequence_step C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_uint32_array_init C.jet_write32s_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_buffer_empty_spec C.jet_sha256_iv_init C.jet_sha256_ctx8_init_spec.
Require Import C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_call C.jet_write_buffer8_empty_cells.
Require Import C.jet_write_buffer8_empty_layout C.jet_write64_then32s_layout C.jet_write_sha256_context_empty_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma ctx8_zero_writer_value : decode_wide W64 (Int64.zero_ext 64 Int64.zero) = @Word.zero 6 Alg.CoreFunSem tt.
Proof. vm_compute; reflexivity. Qed.

Theorem eval_write_sha256_context_empty_layout m bf base bw edge cursor bc cbase bi input :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  0 <= input -> input + 32 <= Ptrofs.max_unsigned ->
  bc <> bf -> bc <> bw -> bi <> bf -> bi <> bw ->
  Mem.load Mint64 m bc (cbase + 8) = Some (Vlong Int64.zero) ->
  Mem.load Mptr m bc cbase = Some (Vptr bi (Ptrofs.repr input)) ->
  Mem.load Mint8unsigned m bc (cbase + 80) = Some (Vint Int.zero) ->
  uint32_array_at m bi input sha256_iv_words ->
  write_frame_at m bf base bw edge cursor 830 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write_sha256_context)
      [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cursor (encode (@sha256_ctx8_init_spec Alg.CoreFunSem tt)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 830) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 830) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM HI HIM Hcf Hcw Hif Hiw HC HO HF HA HW.
  pose proof HW as [HFBase [HFields [HE [HCurs [HMax [Hfw [PW HWords]]]]]]].
  destruct (buffer8_empty_calls_layout m bf base bw edge cursor buffer63_empty_counts 320
    ltac:(lia) buffer63_empty_counts_chain HW)
    as (mb & HRun & HCells & HPrefix & HWNext & HMem & HPerm & HValid).
  rewrite buffer63_empty_bits in HWNext, HMem.
  rewrite buffer63_empty_output_canonical in HCells.
  assert (HBuffer : Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
     Vlong Int64.zero; Vint (Int.repr 5)] E0 mb Vundef).
  { apply eval_write_buffer8_empty_composes; exact HRun. }
  assert (HCb : Mem.load Mint64 mb bc (cbase + 8) = Some (Vlong Int64.zero)).
  { rewrite HMem by (left; assumption). exact HC. }
  assert (HAb : uint32_array_at mb bi input sha256_iv_words).
  { intros i v Hv. rewrite HMem by (left; assumption). exact (HA i v Hv). }
  destruct (eval_write64_then32s_layout mb bi input bf base bw edge (cursor - 510)
    Int64.zero sha256_iv_words HI HIM Hif Hiw HAb HWNext)
    as (mc & mf & HCounter & HIV & HTail & HPrefixTail & HFieldsTail & HMem64 & HMemTail & HPermTail & HValidTail).
  change (frame_fields_at mf bf base bw edge (cursor - 510 - 320)) in HFieldsTail.
  change (loads_outside_ranges mb mf bf (base + 8) (base + 16)
    bw (edge + 8 * ((cursor - 510 - 320) / 64)) (write_word_address edge (cursor - 510) + 8)) in HMemTail.
  assert (HOc : Mem.load Mptr mc bc cbase = Some (Vptr bi (Ptrofs.repr input))).
  { rewrite HMem64 by (left; assumption). rewrite HMem by (left; assumption); exact HO. }
  assert (HFf : Mem.load Mint8unsigned mf bc (cbase + 80) = Some (Vint Int.zero)).
  { rewrite HMemTail by (left; assumption). rewrite HMem by (left; assumption); exact HF. }
  assert (HfirstFinal : frame_output_cells_at mf bw edge cursor (buffer_empty_cells (Word 3) 5)).
  { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
      (cursor := cursor - 510); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HCells].
    rewrite buffer63_byte_cells_length. change (0 <= cursor - 510 <= cursor - 510); lia. }
  assert (HLo : edge + 8 * ((cursor - 830) / 64) <= edge + 8 * ((cursor - 510) / 64)).
  { pose proof (Z.div_le_mono (cursor - 830) (cursor - 510) 64 ltac:(lia) ltac:(lia)); lia. }
  assert (HPrev : write_word_address edge (cursor - 510) <= write_word_address edge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - 510 - 1) (cursor - 1) 64
      ltac:(lia) ltac:(lia)); lia. }
  exists mf. split.
  - eapply eval_write_sha256_context_empty_composes; eauto.
  - split.
    + rewrite sha256_ctx8_init_spec_cells. apply frame_output_cells_at_app. split; [exact HfirstFinal|].
      rewrite buffer63_byte_cells_length. rewrite ctx8_zero_writer_value in HTail. exact HTail.
    + split.
      * eapply write_prefix_at_chain; [exact Hfw| |exact HPrefix|exact HPrefixTail|exact HMemTail]. lia.
      * split.
        -- replace (cursor - 830) with (cursor - 510 - 320) by ring; exact HFieldsTail.
        -- split.
           ++ intros chunk b ofs Hbf Hbw. rewrite HMemTail.
              ** apply HMem; [exact Hbf|]. destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto; lia.
              ** exact Hbf.
              ** replace (cursor - 510 - 320) with (cursor - 830) by ring.
                 destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto; lia.
           ++ split.
              ** intros b ofs kind p HP. apply HPermTail, HPerm; exact HP.
              ** intros b HV. apply HValidTail, HValid; exact HV.
Qed.
