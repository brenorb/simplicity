(** Output steps of the core jets, as [write_effect]s: the actual
    writeBit / write8-16-32-64 calls of the core translation unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_frame_spec C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_writeBit_layout_total C.jet_skipBits_layout C.jet_write_wide_layout_total.
Require C.jets.
Require Import C.jet_bitcoin_effects C.jet_write8_layout_total C.jet_spec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque ge0.
Set Default Timeout 60.

Lemma core_writeBit_step m bf base bw edge cursor (bit : bool) :
  write_frame_at m bf base bw edge cursor 1 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal jets.f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    write_effect m mf bf base bw edge cursor 1 [Some bit].
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_writeBit_layout m bf base bw edge cursor bit HF)
    as (mf & w & HCall & HLoad & HBit & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - exact HCall.
  - split.
    + intros i c Hi. destruct i as [|i]; [|destruct i; discriminate].
      simpl in Hi. injection Hi as Hc. subst c. cbn [cell_matches].
      split; [lia|]. exists w. split.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. exact HLoad.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. symmetry. exact HBit.
    + split; [exact HPrefix|]. split.
      * replace (cursor - 1) with (cursor - 1) by lia. exact HFields.
      * split; [|split; assumption].
        replace (edge + 8 * ((cursor - 1) / 64)) with (write_word_address edge cursor)
          by (unfold write_word_address; reflexivity).
        exact HLoads.
Qed.

Lemma core_write_wide_step s m bf base bw edge cursor x :
  write_frame_at m bf base bw edge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (wide_bits s)
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x))).
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write_wide_layout s m bf base bw edge cursor x HF)
    as (mf & HCall & HSlice & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - exact HCall.
  - split.
    + apply (wide_output_at_encode s); [lia|].
      exists (Int64.zero_ext (wide_bits s) x). split; [exact HSlice|reflexivity].
    + split; [exact HPrefix|]. split; [exact HFields|].
      split; [|split; assumption].
      intros chunk b ofs H1 H2. apply HLoads; [exact H1|].
      pose proof (slice_write_low_bound (wide_bits s) edge cursor (wide_bits_bounds s) ltac:(lia)) as HB.
      destruct H2 as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H].
Qed.

Lemma byte_write_low_cursor edge cursor :
  8 <= cursor -> byte_write_low edge cursor = edge + 8 * ((cursor - 8) / 64).
Proof.
  intros H8. unfold byte_write_low, write_word_address, write_word_shift.
  pose proof (Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)) as HB.
  pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)) as HD.
  destruct (Z_le_dec 8 (1 + (cursor - 1) mod 64)) as [HN|HX].
  - assert (Hq : (cursor - 8) / 64 = (cursor - 1) / 64).
    { symmetry; apply Z.div_unique_pos with (r := (cursor - 1) mod 64 - 7); lia. }
    rewrite Hq. reflexivity.
  - assert (Hq : (cursor - 8) / 64 = (cursor - 1) / 64 - 1).
    { symmetry; apply Z.div_unique_pos with (r := (cursor - 1) mod 64 + 57); lia. }
    rewrite Hq. lia.
Qed.

Lemma core_write8_step m bf base bw edge cursor (x : int) :
  write_frame_at m bf base bw edge cursor 8 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal jets.f_simplicity_write8)
      [Vptr bf (Ptrofs.repr base); Vint x] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 8
      (encode (decode_word8 (Int64.repr (Int.unsigned x)))).
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write8_layout m bf base bw edge cursor x HF)
    as (mf & HCall & HOut & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split; [exact HCall|].
  split.
  - apply byte_output_at_encode; [lia|exact HOut].
  - split; [exact HPrefix|]. split; [exact HFields|].
    split; [|split; assumption].
    rewrite <- (byte_write_low_cursor edge cursor) by lia. exact HLoads.
Qed.
