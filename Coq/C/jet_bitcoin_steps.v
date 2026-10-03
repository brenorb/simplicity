(** Output steps of the Bitcoin getters, as [write_effect]s: the actual
    writeBit / skipBits / write16-32-64 calls of the Bitcoin translation unit,
    obtained from the verified core contracts by transport. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_frame_spec C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_writeBit_layout_total C.jet_skipBits_layout C.jet_write_wide_layout_total.
Require C.jets.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_transport C.jet_bitcoin_effects.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Lemma bitcoin_writeBit_step m bf base bw edge cursor (bit : bool) :
  write_frame_at m bf base bw edge cursor 1 ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal jets.f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    write_effect m mf bf base bw edge cursor 1 [Some bit].
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_writeBit_layout m bf base bw edge cursor bit HF)
    as (mf & w & HCall & HLoad & HBit & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply bitcoin_transport_call; [|exact HCall].
    unfold bitcoin_core_helpers. simpl. tauto.
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

Lemma bitcoin_skipBits_step m bf base bw edge cursor n :
  write_frame_at m bf base bw edge cursor (Z.of_nat n) ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal jets.f_skipBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat n))] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (Z.of_nat n) (repeat None n).
Proof.
  intros HF.
  destruct (eval_skipBits_padding m bf base bw edge cursor n HF)
    as (mf & HCall & HCells & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply bitcoin_transport_call; [|exact HCall].
    unfold bitcoin_core_helpers. simpl. tauto.
  - split; [exact HCells|]. split; [exact HPrefix|]. split; [exact HFields|].
    split; [|split; assumption].
    intros chunk b ofs H1 _. apply HLoads; exact H1.
Qed.

Lemma wide_writer_helper s : exists id, In (id, wide_writer s) bitcoin_core_helpers.
Proof.
  destruct s; [exists jets._simplicity_write16|exists jets._simplicity_write32|exists jets._simplicity_write64];
    unfold bitcoin_core_helpers, wide_writer; simpl; tauto.
Qed.

Lemma bitcoin_write_wide_step s m bf base bw edge cursor x :
  write_frame_at m bf base bw edge cursor (wide_bits s) ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal (wide_writer s))
      [Vptr bf (Ptrofs.repr base); Vlong x] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor (wide_bits s)
      (encode (decode_wide s (Int64.zero_ext (wide_bits s) x))).
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write_wide_layout s m bf base bw edge cursor x HF)
    as (mf & HCall & HSlice & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - destruct (wide_writer_helper s) as [id Hin]. eapply bitcoin_transport_call; eauto.
  - split.
    + apply (wide_output_at_encode s); [lia|].
      exists (Int64.zero_ext (wide_bits s) x). split; [exact HSlice|reflexivity].
    + split; [exact HPrefix|]. split; [exact HFields|].
      split; [|split; assumption].
      intros chunk b ofs H1 H2. apply HLoads; [exact H1|].
      pose proof (slice_write_low_bound (wide_bits s) edge cursor (wide_bits_bounds s) ltac:(lia)) as HB.
      destruct H2 as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H].
Qed.
