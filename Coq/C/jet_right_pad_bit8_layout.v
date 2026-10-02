(** Complete actual right_pad_low_1_8 call, through the shared lifecycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_write8_layout_total C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_canonical C.jet_guarantees C.jet_bit_word_layout C.jet_pad_bit_spec C.jet_right_pad_bit8_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma right_pad_bit8_writer :
  bit_word_writer_contract f_simplicity_write8 (fun b => Vint (right_pad_bit8_arg b))
    (Word 3) (@right_pad_low_1_n 3 Alg.CoreFunSem).
Proof.
  intros m bd dbase bw edge cursor x HF.
  change (Z.of_nat (bitSize (Word 3))) with 8 in *.
  pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_write8_layout m bd dbase bw edge cursor (right_pad_bit8_arg (Bit.toBool x)) HF)
    as (mf & Hcall & Hbyte & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  exists mf. split; [exact Hcall|]. split.
  - apply byte_output_at_encode; [lia|].
    unfold right_pad_bit8_arg in Hbyte. rewrite right_pad_bit8_decode in Hbyte. exact Hbyte.
  - split; [exact Hprefix|]. split; [exact Hfields|]. split; [|auto].
    intros chunk b ofs HB HO. apply Hmemory; [exact HB|]. rewrite byte_write_low_slice.
    pose proof (slice_write_low_bound 8 edge cursor ltac:(lia) ltac:(lia)).
    destruct HO as [HN|[HL|HH]]; [left|right; left|right; right]; auto; lia.
Qed.

Theorem right_pad_low_1_8_local_spec :
  jet_local_spec f_simplicity_right_pad_low_1_8 (Word 0) (Word 3)
    (@right_pad_low_1_n 3 Alg.CoreFunSem).
Proof.
  eapply bit_word_jet_local_spec.
  - apply right_pad_bit8_writer.
  - exact eval_right_pad_bit8_composes.
  - vm_compute; reflexivity.
Qed.
Theorem right_pad_bit8_context :
  jet_context_for f_simplicity_right_pad_low_1_8 (@right_pad_low_1_n 3).
Proof.
  exact (jet_context _ _ (right_pad_low_1_n_parametric 3) right_pad_low_1_8_local_spec ltac:(vm_compute; lia)).
Qed.
Definition right_pad_bit8_guarantees := jet_local_spec_guarantees _ _ _ _ right_pad_low_1_8_local_spec.
Definition right_pad_bit8_context_guarantees :=
  jet_context_guarantees _ _ (right_pad_low_1_n_parametric 3) right_pad_low_1_8_local_spec ltac:(vm_compute; lia).
