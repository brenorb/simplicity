(** Complete right_pad_low_1_{16,32,64} C-to-canonical-program proofs.
    The shared lifecycle's writer and actual-body contracts are discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_canonical C.jet_guarantees C.jet_bit_word_layout C.jet_pad_bit_spec C.jet_right_pad_bit_wide_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma right_pad_bit_wide_writer s :
  bit_word_writer_contract (wide_writer s) (fun b => Vlong (right_pad_bit_long s b))
    (Word (wide_log s)) (@right_pad_low_1_n (wide_log s) Alg.CoreFunSem).
Proof.
  intros m bd dbase bw edge cursor x HF.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in * by (destruct s; reflexivity).
  pose proof (wide_bits_bounds s) as HW. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write_wide_layout s m bd dbase bw edge cursor (right_pad_bit_long s (Bit.toBool x)) HF)
    as (mf & Hcall & Hslice & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  exists mf. split; [exact Hcall|]. split.
  - apply (wide_output_at_encode s); [lia|].
    exists (Int64.zero_ext (wide_bits s) (right_pad_bit_long s (Bit.toBool x))).
    split; [exact Hslice|apply right_pad_bit_wide_decode].
  - split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
    intros chunk b ofs HB HO. apply Hmemory; [exact HB|].
    pose proof (slice_write_low_bound (wide_bits s) edge cursor ltac:(lia) ltac:(lia)).
    destruct HO as [HN|[HL|HH]]; [left|right; left|right; right]; auto; lia.
Qed.

Theorem right_pad_bit_wide_local_spec s :
  jet_local_spec (wide_right_pad_bit s) (Word 0) (Word (wide_log s))
    (@right_pad_low_1_n (wide_log s) Alg.CoreFunSem).
Proof.
  eapply bit_word_jet_local_spec.
  - apply right_pad_bit_wide_writer.
  - unfold bit_word_jet_composer; intros. eapply eval_wide_right_pad_bit_composes; eauto.
  - destruct s; vm_compute; reflexivity.
Qed.
Corollary right_pad_low_1_16_local_spec :
  jet_local_spec f_simplicity_right_pad_low_1_16 (Word 0) (Word 4)
    (@right_pad_low_1_n 4 Alg.CoreFunSem).
Proof. exact (right_pad_bit_wide_local_spec W16). Qed.
Corollary right_pad_low_1_32_local_spec :
  jet_local_spec f_simplicity_right_pad_low_1_32 (Word 0) (Word 5)
    (@right_pad_low_1_n 5 Alg.CoreFunSem).
Proof. exact (right_pad_bit_wide_local_spec W32). Qed.
Corollary right_pad_low_1_64_local_spec :
  jet_local_spec f_simplicity_right_pad_low_1_64 (Word 0) (Word 6)
    (@right_pad_low_1_n 6 Alg.CoreFunSem).
Proof. exact (right_pad_bit_wide_local_spec W64). Qed.
Theorem right_pad_bit_wide_context s :
  jet_context_for (wide_right_pad_bit s) (@right_pad_low_1_n (wide_log s)).
Proof.
  exact (jet_context _ _ (right_pad_low_1_n_parametric (wide_log s))
    (right_pad_bit_wide_local_spec s) ltac:(destruct s; vm_compute; lia)).
Qed.
Definition right_pad_bit_wide_guarantees s :=
  jet_local_spec_guarantees _ _ _ _ (right_pad_bit_wide_local_spec s).
Definition right_pad_bit_wide_context_guarantees s :=
  jet_context_guarantees _ _ (right_pad_low_1_n_parametric (wide_log s))
    (right_pad_bit_wide_local_spec s) ltac:(destruct s; vm_compute; lia).
