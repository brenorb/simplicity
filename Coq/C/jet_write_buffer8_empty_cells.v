(** Connect the actual empty-buffer loop's descending counts to the literal
    bufferEmpty encoding. This is serialization infrastructure, not coverage. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jet_buffer_empty_spec C.jet_write_buffer8_empty_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint buffer8_empty_bits (xs : list Z) : Z := match xs with
  | [] => 0 | j :: xs => 1 + 8 * j + buffer8_empty_bits xs end.
Fixpoint buffer8_empty_output_cells (xs : list Z) : list BitMachine.Cell := match xs with
  | [] => []
  | j :: xs => (Some Datatypes.false :: repeat None (Z.to_nat (8 * j))) ++ buffer8_empty_output_cells xs
  end.

Lemma buffer8_empty_bits_nonnegative xs : buffer8_empty_chain xs -> 0 <= buffer8_empty_bits xs.
Proof.
  induction xs as [|j xs IH]; [cbn; lia|]. intros [HJ [_ HC]].
  cbn [buffer8_empty_bits]. specialize (IH HC); lia.
Qed.
Lemma buffer8_empty_output_length xs : buffer8_empty_chain xs ->
  Z.of_nat (length (buffer8_empty_output_cells xs)) = buffer8_empty_bits xs.
Proof.
  induction xs as [|j xs IH]; [reflexivity|]. intros [HJ [_ HC]].
  cbn [buffer8_empty_output_cells buffer8_empty_bits]. rewrite app_length, Nat2Z.inj_add.
  cbn [length]. rewrite repeat_length, Nat2Z.inj_succ, Z2Nat.id by lia.
  change (buffer8_empty_chain xs -> Z.of_nat (@length (option bool) (buffer8_empty_output_cells xs)) =
    buffer8_empty_bits xs) in IH.
  rewrite (IH HC). lia.
Qed.
Lemma buffer63_empty_bits : buffer8_empty_bits buffer63_empty_counts = 510.
Proof. reflexivity. Qed.
Lemma buffer63_empty_output_canonical : buffer8_empty_output_cells buffer63_empty_counts =
  buffer_empty_cells (Word 3) 5.
Proof. vm_compute; reflexivity. Qed.
