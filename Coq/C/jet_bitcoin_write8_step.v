(** The actual [simplicity_write8] call of the Bitcoin translation unit as a
    [write_effect], obtained from the verified core contract by transport. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_frame_spec C.jet_spec C.jet_encoding C.jet_write8_layout_total.
Require C.jets.
Require Import C.jet_bitcoin_linkage C.jet_bitcoin_transport C.jet_bitcoin_effects.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

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

Lemma bitcoin_write8_step m bf base bw edge cursor (x : int) :
  write_frame_at m bf base bw edge cursor 8 ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal jets.f_simplicity_write8)
      [Vptr bf (Ptrofs.repr base); Vint x] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 8
      (encode (decode_word8 (Int64.repr (Int.unsigned x)))).
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write8_layout m bf base bw edge cursor x HF)
    as (mf & HCall & HOut & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply bitcoin_transport_call; [|exact HCall].
    unfold bitcoin_core_helpers. simpl. tauto.
  - split.
    + apply byte_output_at_encode; [lia|exact HOut].
    + split; [exact HPrefix|]. split; [exact HFields|].
      split; [|split; assumption].
      rewrite <- (byte_write_low_cursor edge cursor) by lia. exact HLoads.
Qed.
