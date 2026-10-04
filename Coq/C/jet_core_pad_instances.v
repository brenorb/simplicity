(** The 32 core padding jets left/right_pad_low/high_n_m (n >= 8) and
    left/right_pad_high_1_m against the literal Programs.Word padding terms,
    as separated local contracts without an external-library premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_context_separated C.jet_bitcoin_effects.
Require Import C.jet_core_wrapper C.jet_core_copy_exec C.jet_core_loop C.jet_core_pad_spec C.jet_core_pad_steps.
Require Import C.jet_core_pad C.jet_core_pad_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 120.

Lemma core_src_locals_other bl id : id <> _src -> (core_src_locals bl)!id = None.
Proof. intros H. unfold core_src_locals. rewrite PTree.gso by exact H. apply PTree.gempty. Qed.

Lemma pad_disjoint_i : list_disjoint [_dst; _src; _env] [_i].
Proof.
  intros x y Hx Hy Hxy. cbn in Hx, Hy.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Theorem left_pad_low_8_16_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_8_16 (Word 3) (Word 4) (@left_pad_low_spec Alg.CoreFunSem 3 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 8) (Nn := 8) (cnt := pad_count_expr 16 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 3 1 a).
Qed.

Theorem left_pad_low_8_32_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_8_32 (Word 3) (Word 5) (@left_pad_low_spec Alg.CoreFunSem 3 2).
Proof.
  eapply core_left_pad_jet with (c := 3) (w := 8) (Nn := 8) (cnt := pad_count_expr 32 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 3 2 a).
Qed.

Theorem left_pad_low_16_32_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_16_32 (Word 4) (Word 5) (@left_pad_low_spec Alg.CoreFunSem 4 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 16) (Nn := 16) (cnt := pad_count_expr 32 16) (stmt := pad16_0_stmt) (pcells := (repeat (Some Datatypes.false) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 4 1 a).
Qed.

Theorem left_pad_low_8_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_8_64 (Word 3) (Word 6) (@left_pad_low_spec Alg.CoreFunSem 3 3).
Proof.
  eapply core_left_pad_jet with (c := 7) (w := 8) (Nn := 8) (cnt := pad_count_expr 64 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 3 3 a).
Qed.

Theorem left_pad_low_16_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_16_64 (Word 4) (Word 6) (@left_pad_low_spec Alg.CoreFunSem 4 2).
Proof.
  eapply core_left_pad_jet with (c := 3) (w := 16) (Nn := 16) (cnt := pad_count_expr 64 16) (stmt := pad16_0_stmt) (pcells := (repeat (Some Datatypes.false) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 4 2 a).
Qed.

Theorem left_pad_low_32_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_low_32_64 (Word 5) (Word 6) (@left_pad_low_spec Alg.CoreFunSem 5 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 32) (Nn := 32) (cnt := pad_count_expr 64 32) (stmt := pad32_0_stmt) (pcells := (repeat (Some Datatypes.false) 32));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad32_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_low 5 1 a).
Qed.

Theorem left_pad_high_8_16_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_8_16 (Word 3) (Word 4) (@left_pad_high_spec Alg.CoreFunSem 3 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 8) (Nn := 8) (cnt := pad_count_expr 16 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 3 1 a).
Qed.

Theorem left_pad_high_8_32_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_8_32 (Word 3) (Word 5) (@left_pad_high_spec Alg.CoreFunSem 3 2).
Proof.
  eapply core_left_pad_jet with (c := 3) (w := 8) (Nn := 8) (cnt := pad_count_expr 32 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 3 2 a).
Qed.

Theorem left_pad_high_16_32_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_16_32 (Word 4) (Word 5) (@left_pad_high_spec Alg.CoreFunSem 4 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 16) (Nn := 16) (cnt := pad_count_expr 32 16) (stmt := pad16_max_stmt) (pcells := (repeat (Some Datatypes.true) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 4 1 a).
Qed.

Theorem left_pad_high_8_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_8_64 (Word 3) (Word 6) (@left_pad_high_spec Alg.CoreFunSem 3 3).
Proof.
  eapply core_left_pad_jet with (c := 7) (w := 8) (Nn := 8) (cnt := pad_count_expr 64 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 3 3 a).
Qed.

Theorem left_pad_high_16_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_16_64 (Word 4) (Word 6) (@left_pad_high_spec Alg.CoreFunSem 4 2).
Proof.
  eapply core_left_pad_jet with (c := 3) (w := 16) (Nn := 16) (cnt := pad_count_expr 64 16) (stmt := pad16_max_stmt) (pcells := (repeat (Some Datatypes.true) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 4 2 a).
Qed.

Theorem left_pad_high_32_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_32_64 (Word 5) (Word 6) (@left_pad_high_spec Alg.CoreFunSem 5 1).
Proof.
  eapply core_left_pad_jet with (c := 1) (w := 32) (Nn := 32) (cnt := pad_count_expr 64 32) (stmt := pad32_max_stmt) (pcells := (repeat (Some Datatypes.true) 32));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad32_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 5 1 a).
Qed.

Theorem left_pad_high_1_8_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_1_8 (Word 0) (Word 3) (@left_pad_high_spec Alg.CoreFunSem 0 3).
Proof.
  eapply core_left_pad_jet with (c := 7) (w := 1) (Nn := 1) (cnt := pad_count_expr1 8) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 0 3 a).
Qed.

Theorem left_pad_high_1_16_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_1_16 (Word 0) (Word 4) (@left_pad_high_spec Alg.CoreFunSem 0 4).
Proof.
  eapply core_left_pad_jet with (c := 15) (w := 1) (Nn := 1) (cnt := pad_count_expr1 16) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 0 4 a).
Qed.

Theorem left_pad_high_1_32_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_1_32 (Word 0) (Word 5) (@left_pad_high_spec Alg.CoreFunSem 0 5).
Proof.
  eapply core_left_pad_jet with (c := 31) (w := 1) (Nn := 1) (cnt := pad_count_expr1 32) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 0 5 a).
Qed.

Theorem left_pad_high_1_64_local_spec :
  jet_separated_local_spec f_simplicity_left_pad_high_1_64 (Word 0) (Word 6) (@left_pad_high_spec Alg.CoreFunSem 0 6).
Proof.
  eapply core_left_pad_jet with (c := 63) (w := 1) (Nn := 1) (cnt := pad_count_expr1 64) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_left_pad_high 0 6 a).
Qed.

Theorem right_pad_low_8_16_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_8_16 (Word 3) (Word 4) (@right_pad_low_spec Alg.CoreFunSem 3 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 8) (Nn := 8) (cnt := pad_count_expr 16 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 3 1 a).
Qed.

Theorem right_pad_low_8_32_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_8_32 (Word 3) (Word 5) (@right_pad_low_spec Alg.CoreFunSem 3 2).
Proof.
  eapply core_right_pad_jet with (c := 3) (w := 8) (Nn := 8) (cnt := pad_count_expr 32 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 3 2 a).
Qed.

Theorem right_pad_low_16_32_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_16_32 (Word 4) (Word 5) (@right_pad_low_spec Alg.CoreFunSem 4 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 16) (Nn := 16) (cnt := pad_count_expr 32 16) (stmt := pad16_0_stmt) (pcells := (repeat (Some Datatypes.false) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 4 1 a).
Qed.

Theorem right_pad_low_8_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_8_64 (Word 3) (Word 6) (@right_pad_low_spec Alg.CoreFunSem 3 3).
Proof.
  eapply core_right_pad_jet with (c := 7) (w := 8) (Nn := 8) (cnt := pad_count_expr 64 8) (stmt := pad8_0_stmt) (pcells := (repeat (Some Datatypes.false) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 3 3 a).
Qed.

Theorem right_pad_low_16_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_16_64 (Word 4) (Word 6) (@right_pad_low_spec Alg.CoreFunSem 4 2).
Proof.
  eapply core_right_pad_jet with (c := 3) (w := 16) (Nn := 16) (cnt := pad_count_expr 64 16) (stmt := pad16_0_stmt) (pcells := (repeat (Some Datatypes.false) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 4 2 a).
Qed.

Theorem right_pad_low_32_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_low_32_64 (Word 5) (Word 6) (@right_pad_low_spec Alg.CoreFunSem 5 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 32) (Nn := 32) (cnt := pad_count_expr 64 32) (stmt := pad32_0_stmt) (pcells := (repeat (Some Datatypes.false) 32));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad32_0_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_low 5 1 a).
Qed.

Theorem right_pad_high_8_16_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_8_16 (Word 3) (Word 4) (@right_pad_high_spec Alg.CoreFunSem 3 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 8) (Nn := 8) (cnt := pad_count_expr 16 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 3 1 a).
Qed.

Theorem right_pad_high_8_32_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_8_32 (Word 3) (Word 5) (@right_pad_high_spec Alg.CoreFunSem 3 2).
Proof.
  eapply core_right_pad_jet with (c := 3) (w := 8) (Nn := 8) (cnt := pad_count_expr 32 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 3 2 a).
Qed.

Theorem right_pad_high_16_32_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_16_32 (Word 4) (Word 5) (@right_pad_high_spec Alg.CoreFunSem 4 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 16) (Nn := 16) (cnt := pad_count_expr 32 16) (stmt := pad16_max_stmt) (pcells := (repeat (Some Datatypes.true) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 4 1 a).
Qed.

Theorem right_pad_high_8_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_8_64 (Word 3) (Word 6) (@right_pad_high_spec Alg.CoreFunSem 3 3).
Proof.
  eapply core_right_pad_jet with (c := 7) (w := 8) (Nn := 8) (cnt := pad_count_expr 64 8) (stmt := pad8_255_stmt) (pcells := (repeat (Some Datatypes.true) 8));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad8_255_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 3 3 a).
Qed.

Theorem right_pad_high_16_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_16_64 (Word 4) (Word 6) (@right_pad_high_spec Alg.CoreFunSem 4 2).
Proof.
  eapply core_right_pad_jet with (c := 3) (w := 16) (Nn := 16) (cnt := pad_count_expr 64 16) (stmt := pad16_max_stmt) (pcells := (repeat (Some Datatypes.true) 16));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad16_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 4 2 a).
Qed.

Theorem right_pad_high_32_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_32_64 (Word 5) (Word 6) (@right_pad_high_spec Alg.CoreFunSem 5 1).
Proof.
  eapply core_right_pad_jet with (c := 1) (w := 32) (Nn := 32) (cnt := pad_count_expr 64 32) (stmt := pad32_max_stmt) (pcells := (repeat (Some Datatypes.true) 32));
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply pad32_max_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 5 1 a).
Qed.

Theorem right_pad_high_1_8_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_1_8 (Word 0) (Word 3) (@right_pad_high_spec Alg.CoreFunSem 0 3).
Proof.
  eapply core_right_pad_jet with (c := 7) (w := 1) (Nn := 1) (cnt := pad_count_expr1 8) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 0 3 a).
Qed.

Theorem right_pad_high_1_16_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_1_16 (Word 0) (Word 4) (@right_pad_high_spec Alg.CoreFunSem 0 4).
Proof.
  eapply core_right_pad_jet with (c := 15) (w := 1) (Nn := 1) (cnt := pad_count_expr1 16) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 0 4 a).
Qed.

Theorem right_pad_high_1_32_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_1_32 (Word 0) (Word 5) (@right_pad_high_spec Alg.CoreFunSem 0 5).
Proof.
  eapply core_right_pad_jet with (c := 31) (w := 1) (Nn := 1) (cnt := pad_count_expr1 32) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 0 5 a).
Qed.

Theorem right_pad_high_1_64_local_spec :
  jet_separated_local_spec f_simplicity_right_pad_high_1_64 (Word 0) (Word 6) (@right_pad_high_spec Alg.CoreFunSem 0 6).
Proof.
  eapply core_right_pad_jet with (c := 63) (w := 1) (Nn := 1) (cnt := pad_count_expr1 64) (stmt := padbit_true_stmt) (pcells := [Some Datatypes.true]);
    [ | | | | | | | | | | ].
  - repeat split; try reflexivity. apply pad_disjoint_i.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - intros e le m'; apply eval_pad_count_expr1; lia.
  - intros bl le' m cur bd dbase bw edge Hd HF.
    eapply padbit_true_step; [apply core_src_locals_other; vm_compute; discriminate|exact Hd|exact HF].
  - intros a. exact (encode_right_pad_high 0 6 a).
Qed.
