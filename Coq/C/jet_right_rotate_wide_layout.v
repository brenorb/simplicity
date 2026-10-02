(** Complete right_rotate_32/64 C-to-canonical-Simplicity contracts.
    Initial frames suffice; cursor crossings and arbitrary output contents
    are allowed. Scalar helper calls, writes and cleanup are all discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Ctypes Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_context C.jet_canonical C.jet_guarantees.
Require Import C.jet_left_rotate_wide_exec C.jet_right_rotate_wide_exec C.jet_right_rotate_wide_layout_machine.
Require Import C.jet_right_rotate_spec C.jet_right_rotate_wide_word.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem right_rotate_byte_local_spec s :
  jet_local_spec (right_rotate_byte_function s)
    (Ty.Prod (Word 3) (Word (wide_log (byte_rotate_width s))))
    (Word (wide_log (byte_rotate_width s)))
    (fun ax => @right_rotate_byte_spec s Alg.CoreFunSem ax).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [amount x]
    HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Ty.Prod (Word 3) (Word (wide_log (byte_rotate_width s))))))
    with (8 + wide_bits (byte_rotate_width s)) in * by (destruct s; reflexivity).
  replace (Z.of_nat (bitSize (Word (wide_log (byte_rotate_width s)))))
    with (wide_bits (byte_rotate_width s)) in * by (destruct s; reflexivity).
  change (frame_input_cells_at m bi edge rc (encode amount ++ encode x)) in Hin.
  rewrite frame_input_cells_at_app, encode_length in Hin.
  change (Z.of_nat (bitSize (Word 3))) with 8 in Hin.
  destruct Hin as [Hamount Hinput].
  apply frame_input_word_at_encode in Hamount.
  apply frame_input_word_at_encode in Hinput.
  pose proof (eval_right_rotate_byte_layout_machine env s m bd dbase bs sbase bi bw edge outedge
    amount x cursor rc HB HA HF ltac:(lia) Hamount Hinput Hout) as H.
  rewrite right_rotate_byte_machine_denotes in H. exact H.
Qed.

Corollary right_rotate32_local_spec : jet_local_spec f_simplicity_right_rotate_32
  (Ty.Prod (Word 3) (Word 5)) (Word 5)
  (fun ax => @right_rotate_byte_spec R32 Alg.CoreFunSem ax).
Proof. exact (right_rotate_byte_local_spec R32). Qed.

Corollary right_rotate64_local_spec : jet_local_spec f_simplicity_right_rotate_64
  (Ty.Prod (Word 3) (Word 6)) (Word 6)
  (fun ax => @right_rotate_byte_spec R64 Alg.CoreFunSem ax).
Proof. exact (right_rotate_byte_local_spec R64). Qed.

Theorem right_rotate_byte_context s :
  jet_context_for (right_rotate_byte_function s) (@right_rotate_byte_spec s).
Proof.
  exact (jet_context _ _ (right_rotate_byte_spec_parametric s) (right_rotate_byte_local_spec s)
    ltac:(destruct s; vm_compute; lia)).
Qed.

Definition right_rotate_byte_guarantees s :=
  jet_local_spec_guarantees _ _ _ _ (right_rotate_byte_local_spec s).
Definition right_rotate_byte_context_guarantees s :=
  jet_context_guarantees _ _ (right_rotate_byte_spec_parametric s) (right_rotate_byte_local_spec s)
    ltac:(destruct s; vm_compute; lia).

