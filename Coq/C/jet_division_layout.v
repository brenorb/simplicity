(** Actual C divide/modulo calls against the literal canonical Simplicity
    programs, with arbitrary valid frames, cursors and initial output bits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_spec C.jet_frame_spec C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_wide.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_guarantees.
Require Import C.jet_canonical.
Require Import C.jet_division8_exec C.jet_division_wide_exec.
Require Import C.jet_division8_layout_machine C.jet_division_wide_layout_machine.
Require Import C.jet_division_result_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem division8_local_spec remainder :
  jet_local_spec (division8 remainder) (Ty.Prod Word8 Word8) Word8
    (fun xy => @division_word_spec 3 remainder Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Word8)) with 8 in *.
  change (Z.of_nat (bitSize (Ty.Prod Word8 Word8))) with 16 in Hmax.
  assert (Hbytes : byte_input_at m bs sbase bi edge rc [x; y]).
  { apply byte_input_pair_encode. split; [exact HB|]. split; [exact HF|]. split; [lia|exact Hin]. }
  destruct (byte_input_pair_at _ _ _ _ _ _ _ _ Hbytes) as [_ [_ [HX HY]]].
  destruct (eval_division8_layout_machine env remainder m bd dbase bs sbase bi bw edge outedge
    x y cursor rc HB HA HF HX HY Hout) as (mf & Hcall & Hobs & Hpre & Hfields & Hmemory).
  rewrite division_word_representation in Hobs.
  exists mf. split; [exact Hcall|]. split; [exact Hobs|].
  split; [exact Hpre|]. split; [exact Hfields|exact Hmemory].
Qed.

Theorem wide_division_local_spec remainder s :
  jet_local_spec (wide_division remainder s) (Ty.Prod (Word (wide_log s)) (Word (wide_log s)))
    (Word (wide_log s)) (fun xy => @division_word_spec (wide_log s) remainder Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in * by (destruct s; reflexivity).
  replace (Z.of_nat (bitSize (Ty.Prod (Word (wide_log s)) (Word (wide_log s))))) with
    (2 * wide_bits s) in Hmax by (destruct s; reflexivity).
  apply frame_input_word_pair_encode in Hin. destruct Hin as [HX HY].
  replace (Z.of_nat (Nat.pow 2 (wide_log s))) with (wide_bits s) in HY by (destruct s; reflexivity).
  destruct (eval_wide_division_layout_machine env remainder s m bd dbase bs sbase bi bw edge outedge
    x y cursor rc HB HA HF ltac:(lia) HX HY Hout) as (mf & Hcall & Hobs & Hpre & Hfields & Hmemory).
  rewrite division_word_representation in Hobs.
  exists mf. split; [exact Hcall|]. split; [exact Hobs|].
  split; [exact Hpre|]. split; [exact Hfields|exact Hmemory].
Qed.

Corollary divide8_local_spec : jet_local_spec f_simplicity_divide_8 (Ty.Prod Word8 Word8) Word8
  (fun xy => @division_word_spec 3 Datatypes.false Alg.CoreFunSem xy).
Proof. exact (division8_local_spec Datatypes.false). Qed.
Corollary modulo8_local_spec : jet_local_spec f_simplicity_modulo_8 (Ty.Prod Word8 Word8) Word8
  (fun xy => @division_word_spec 3 Datatypes.true Alg.CoreFunSem xy).
Proof. exact (division8_local_spec Datatypes.true). Qed.
Corollary divide16_local_spec : jet_local_spec f_simplicity_divide_16 (Ty.Prod (Word 4) (Word 4)) (Word 4)
  (fun xy => @division_word_spec 4 Datatypes.false Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.false W16). Qed.
Corollary modulo16_local_spec : jet_local_spec f_simplicity_modulo_16 (Ty.Prod (Word 4) (Word 4)) (Word 4)
  (fun xy => @division_word_spec 4 Datatypes.true Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.true W16). Qed.
Corollary divide32_local_spec : jet_local_spec f_simplicity_divide_32 (Ty.Prod (Word 5) (Word 5)) (Word 5)
  (fun xy => @division_word_spec 5 Datatypes.false Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.false W32). Qed.
Corollary modulo32_local_spec : jet_local_spec f_simplicity_modulo_32 (Ty.Prod (Word 5) (Word 5)) (Word 5)
  (fun xy => @division_word_spec 5 Datatypes.true Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.true W32). Qed.
Corollary divide64_local_spec : jet_local_spec f_simplicity_divide_64 (Ty.Prod (Word 6) (Word 6)) (Word 6)
  (fun xy => @division_word_spec 6 Datatypes.false Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.false W64). Qed.
Corollary modulo64_local_spec : jet_local_spec f_simplicity_modulo_64 (Ty.Prod (Word 6) (Word 6)) (Word 6)
  (fun xy => @division_word_spec 6 Datatypes.true Alg.CoreFunSem xy).
Proof. exact (wide_division_local_spec Datatypes.true W64). Qed.

Theorem division8_context remainder : jet_context_for (division8 remainder) (@division_word_spec 3 remainder).
Proof.
  exact (jet_context _ _ (division_word_spec_parametric 3 remainder) (division8_local_spec remainder)
    ltac:(vm_compute; lia)).
Qed.
Theorem wide_division_context remainder s :
  jet_context_for (wide_division remainder s) (@division_word_spec (wide_log s) remainder).
Proof.
  exact (jet_context _ _ (division_word_spec_parametric (wide_log s) remainder)
    (wide_division_local_spec remainder s) ltac:(destruct s; vm_compute; lia)).
Qed.
Definition division8_guarantees remainder :=
  jet_local_spec_guarantees _ _ _ _ (division8_local_spec remainder).
Definition division8_context_guarantees remainder :=
  jet_context_guarantees _ _ (division_word_spec_parametric 3 remainder) (division8_local_spec remainder)
    ltac:(vm_compute; lia).
Definition wide_division_guarantees remainder s :=
  jet_local_spec_guarantees _ _ _ _ (wide_division_local_spec remainder s).
Definition wide_division_context_guarantees remainder s :=
  jet_context_guarantees _ _ (division_word_spec_parametric (wide_log s) remainder)
    (wide_division_local_spec remainder s) ltac:(destruct s; vm_compute; lia).
