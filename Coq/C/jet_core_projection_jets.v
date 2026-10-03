(** The 36 core projection jets leftmost_n_m / rightmost_n_m against the
    canonical Simplicity programs [leftmost] / [rightmost] over vectors, as
    separated local contracts conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_context_separated C.jet_projection_cells.
Require Import C.jet_core_wrapper C.jet_core_copy_exec C.jet_core_copy_jets C.jet_memcpy_model.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Theorem leftmost_8_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_8_1 (Word 3) (Word 0) (@leftmost (Word 0) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 0))) with 1. lia.
  - change (bitSize (Word 0)) with 1%nat. change (bitSize (Word 3)) with 8%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_8_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_8_2 (Word 3) (Word 1) (@leftmost (Word 1) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 1))) with 2. lia.
  - change (bitSize (Word 1)) with 2%nat. change (bitSize (Word 3)) with 8%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_8_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_8_4 (Word 3) (Word 2) (@leftmost (Word 2) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 2))) with 4. lia.
  - change (bitSize (Word 2)) with 4%nat. change (bitSize (Word 3)) with 8%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_16_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_16_1 (Word 4) (Word 0) (@leftmost (Word 0) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 0))) with 1. lia.
  - change (bitSize (Word 0)) with 1%nat. change (bitSize (Word 4)) with 16%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_16_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_16_2 (Word 4) (Word 1) (@leftmost (Word 1) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 1))) with 2. lia.
  - change (bitSize (Word 1)) with 2%nat. change (bitSize (Word 4)) with 16%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_16_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_16_4 (Word 4) (Word 2) (@leftmost (Word 2) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 2))) with 4. lia.
  - change (bitSize (Word 2)) with 4%nat. change (bitSize (Word 4)) with 16%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_16_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_16_8 (Word 4) (Word 3) (@leftmost (Word 3) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 3))) with 8. lia.
  - change (bitSize (Word 3)) with 8%nat. change (bitSize (Word 4)) with 16%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_32_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_32_1 (Word 5) (Word 0) (@leftmost (Word 0) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 0))) with 1. lia.
  - change (bitSize (Word 0)) with 1%nat. change (bitSize (Word 5)) with 32%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_32_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_32_2 (Word 5) (Word 1) (@leftmost (Word 1) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 1))) with 2. lia.
  - change (bitSize (Word 1)) with 2%nat. change (bitSize (Word 5)) with 32%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_32_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_32_4 (Word 5) (Word 2) (@leftmost (Word 2) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 2))) with 4. lia.
  - change (bitSize (Word 2)) with 4%nat. change (bitSize (Word 5)) with 32%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_32_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_32_8 (Word 5) (Word 3) (@leftmost (Word 3) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 3))) with 8. lia.
  - change (bitSize (Word 3)) with 8%nat. change (bitSize (Word 5)) with 32%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_32_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_32_16 (Word 5) (Word 4) (@leftmost (Word 4) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 4))) with 16. lia.
  - change (bitSize (Word 4)) with 16%nat. change (bitSize (Word 5)) with 32%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_1 (Word 6) (Word 0) (@leftmost (Word 0) 6 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 0))) with 1. lia.
  - change (bitSize (Word 0)) with 1%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_2 (Word 6) (Word 1) (@leftmost (Word 1) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 1))) with 2. lia.
  - change (bitSize (Word 1)) with 2%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_4 (Word 6) (Word 2) (@leftmost (Word 2) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 2))) with 4. lia.
  - change (bitSize (Word 2)) with 4%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_8 (Word 6) (Word 3) (@leftmost (Word 3) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 3))) with 8. lia.
  - change (bitSize (Word 3)) with 8%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_16 (Word 6) (Word 4) (@leftmost (Word 4) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 4))) with 16. lia.
  - change (bitSize (Word 4)) with 16%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem leftmost_64_32_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_leftmost_64_32 (Word 6) (Word 5) (@leftmost (Word 5) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet; [exact Hm| | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - change (Z.of_nat (bitSize (Word 5))) with 32. lia.
  - change (bitSize (Word 5)) with 32%nat. change (bitSize (Word 6)) with 64%nat. lia.
  - intros a. apply encode_leftmost.
Qed.

Theorem rightmost_8_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_8_1 (Word 3) (Word 0) (@rightmost (Word 0) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 8) (M := 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_8_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_8_2 (Word 3) (Word 1) (@rightmost (Word 1) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 8) (M := 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_8_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_8_4 (Word 3) (Word 2) (@rightmost (Word 2) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 8) (M := 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_16_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_16_1 (Word 4) (Word 0) (@rightmost (Word 0) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 16) (M := 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_16_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_16_2 (Word 4) (Word 1) (@rightmost (Word 1) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 16) (M := 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_16_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_16_4 (Word 4) (Word 2) (@rightmost (Word 2) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 16) (M := 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_16_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_16_8 (Word 4) (Word 3) (@rightmost (Word 3) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 16) (M := 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_32_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_32_1 (Word 5) (Word 0) (@rightmost (Word 0) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 32) (M := 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_32_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_32_2 (Word 5) (Word 1) (@rightmost (Word 1) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 32) (M := 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_32_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_32_4 (Word 5) (Word 2) (@rightmost (Word 2) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 32) (M := 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_32_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_32_8 (Word 5) (Word 3) (@rightmost (Word 3) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 32) (M := 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_32_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_32_16 (Word 5) (Word 4) (@rightmost (Word 4) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 32) (M := 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_1 (Word 6) (Word 0) (@rightmost (Word 0) 6 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_2 (Word 6) (Word 1) (@rightmost (Word 1) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_4 (Word 6) (Word 2) (@rightmost (Word 2) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_8 (Word 6) (Word 3) (@rightmost (Word 3) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_16 (Word 6) (Word 4) (@rightmost (Word 4) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.

Theorem rightmost_64_32_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_rightmost_64_32 (Word 6) (Word 5) (@rightmost (Word 5) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_rightmost_jet with (N := 64) (M := 32); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - intros a. rewrite encode_rightmost. reflexivity.
Qed.
