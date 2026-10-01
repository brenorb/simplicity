(** Uniform, total constant writers, observed through canonical encoding.
    All stores, crossing-word accesses and permissions come from the existing
    total writers. No assumptions about initial output values are introduced. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_frame_spec C.jet_output_slice C.jet_wide C.jet_wide_spec C.jet_spec.
Require Import C.jet_writeBit_layout_total C.jet_write8_layout_total C.jet_write_wide_layout_total.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_canonical C.jet_constant.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_constant_writer s high m bf base bw edge cursor :
  write_frame_at m bf base bw edge cursor (constant_bits s) ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal (constant_writer s))
      [Vptr bf (Ptrofs.repr base); constant_value s high] E0 mf (constant_return s high) /\
    frame_output_cells_at mf bw edge cursor (encode (@constant_spec s high Alg.CoreFunSem tt)) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - constant_bits s) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - constant_bits s) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HFrame. pose proof (write_frame_at_count _ _ _ _ _ _ _ HFrame) as HC.
  destruct s; cbn [constant_bits] in HC, HFrame.
  - destruct (eval_writeBit_layout m bf base bw edge cursor high HFrame)
      as (mf & w & Hcall & Hload & Hbit & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    exists mf. split.
    + destruct high; exact Hcall.
    + split.
      * apply carry_output_encode; [exact HC|]. exists w. split; [exact Hload|].
        rewrite Hbit. destruct high; reflexivity.
      * split; [exact Hprefix|]. split; [exact Hfields|]. split; [exact Hmemory|]. auto.
  - destruct (eval_write8_layout m bf base bw edge cursor (Int.repr (constant_unsigned C8 high)) HFrame)
      as (mf & Hcall & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    exists mf. split; [exact Hcall|]. split.
    + apply byte_output_at_encode; [exact HC|]. rewrite constant_decode8 in Houtput. exact Houtput.
    + split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
      intros chunk b ofs HB HW. apply Hmemory; [exact HB|].
      rewrite byte_write_low_slice. pose proof (slice_write_low_bound 8 edge cursor ltac:(lia) HC).
      cbn [constant_bits] in HW.
      destruct HW as [HW|[HW|HW]]; [left|right; left|right; right]; auto; lia.
  - destruct (eval_write_wide_layout W16 m bf base bw edge cursor
        (Int64.repr (constant_unsigned C16 high)) HFrame)
      as (mf & Hcall & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    exists mf. split; [exact Hcall|]. split.
    + apply (wide_output_at_encode W16); [exact HC|].
      eexists. split; [exact Houtput|apply constant_decode16].
    + split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
      intros chunk b ofs HB HW. apply Hmemory; [exact HB|].
      pose proof (slice_write_low_bound 16 edge cursor ltac:(lia) HC).
      cbn [constant_bits wide_bits] in HW |- *.
      destruct HW as [HW|[HW|HW]]; [left|right; left|right; right]; auto; lia.
  - destruct (eval_write_wide_layout W32 m bf base bw edge cursor
        (Int64.repr (constant_unsigned C32 high)) HFrame)
      as (mf & Hcall & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    exists mf. split; [exact Hcall|]. split.
    + apply (wide_output_at_encode W32); [exact HC|].
      eexists. split; [exact Houtput|apply constant_decode32].
    + split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
      intros chunk b ofs HB HW. apply Hmemory; [exact HB|].
      pose proof (slice_write_low_bound 32 edge cursor ltac:(lia) HC).
      cbn [constant_bits wide_bits] in HW |- *.
      destruct HW as [HW|[HW|HW]]; [left|right; left|right; right]; auto; lia.
  - destruct (eval_write_wide_layout W64 m bf base bw edge cursor
        (Int64.repr (constant_unsigned C64 high)) HFrame)
      as (mf & Hcall & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    exists mf. split; [exact Hcall|]. split.
    + apply (wide_output_at_encode W64); [exact HC|].
      eexists. split; [exact Houtput|apply constant_decode64].
    + split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
      intros chunk b ofs HB HW. apply Hmemory; [exact HB|].
      pose proof (slice_write_low_bound 64 edge cursor ltac:(lia) HC).
      cbn [constant_bits wide_bits] in HW |- *.
      destruct HW as [HW|[HW|HW]]; [left|right; left|right; right]; auto; lia.
Qed.
