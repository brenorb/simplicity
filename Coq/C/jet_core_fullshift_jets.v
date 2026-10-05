(** The core full_left_shift_n_m / full_right_shift_n_m jets whose copy count
    n + m is at most 64 bits.  Their canonical programs only rebalance the
    tuple, so the serialized output equals the input; the jets copy all input
    cells.  Conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_context_separated C.jet_full_shift_cells.
Require Import C.jet_core_wrapper C.jet_core_copy_exec C.jet_core_copy_jets C.jet_memcpy_model.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma core_fullshift_left_encode X n (a : Ty.tySem (Ty.Prod (Vector X n) X)) :
  encode (@full_left_shift1 X n Alg.CoreFunSem a) = @encode (Ty.Prod (Vector X n) X) a.
Proof. destruct a as [v x]. apply encode_full_left_shift1. Qed.

Lemma core_fullshift_right_encode X n (a : Ty.tySem (Ty.Prod X (Vector X n))) :
  encode (@full_right_shift1 X n Alg.CoreFunSem a) = @encode (Ty.Prod X (Vector X n)) a.
Proof. destruct a as [x v]. apply encode_full_right_shift1. Qed.

Definition fullshift_arg (N M : Z) : expr :=
  Ebinop Oadd (Econst_int (Int.repr N) tint) (Econst_int (Int.repr M) tint) tint.

Lemma eval_fullshift_arg e le m N M :
  0 <= N <= 64 -> 0 <= M <= 64 ->
  eval_expr ge0 e le m (fullshift_arg N M) (Vint (Int.repr (N + M))).
Proof.
  intros HN HM. unfold fullshift_arg.
  eapply eval_Ebinop with (v1 := Vint (Int.repr N)) (v2 := Vint (Int.repr M));
    [apply eval_Econst_int|apply eval_Econst_int|].
  simpl. unfold sem_add, sem_binarith, sem_cast. simpl.
  f_equal. f_equal. rewrite Int.add_unsigned. apply Int.eqm_samerepr.
  apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Theorem full_left_shift_8_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_8_1 (Ty.Prod (Word 3) (Word 0)) (Ty.Prod (Word 0) (Word 3)) (@full_left_shift1 (Word 0) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 0) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_8_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_8_2 (Ty.Prod (Word 3) (Word 1)) (Ty.Prod (Word 1) (Word 3)) (@full_left_shift1 (Word 1) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 1) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_8_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_8_4 (Ty.Prod (Word 3) (Word 2)) (Ty.Prod (Word 2) (Word 3)) (@full_left_shift1 (Word 2) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 2) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_16_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_16_1 (Ty.Prod (Word 4) (Word 0)) (Ty.Prod (Word 0) (Word 4)) (@full_left_shift1 (Word 0) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 0) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_16_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_16_2 (Ty.Prod (Word 4) (Word 1)) (Ty.Prod (Word 1) (Word 4)) (@full_left_shift1 (Word 1) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 1) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_16_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_16_4 (Ty.Prod (Word 4) (Word 2)) (Ty.Prod (Word 2) (Word 4)) (@full_left_shift1 (Word 2) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 2) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_16_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_16_8 (Ty.Prod (Word 4) (Word 3)) (Ty.Prod (Word 3) (Word 4)) (@full_left_shift1 (Word 3) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 8 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 3) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_32_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_32_1 (Ty.Prod (Word 5) (Word 0)) (Ty.Prod (Word 0) (Word 5)) (@full_left_shift1 (Word 0) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 0) 5 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_32_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_32_2 (Ty.Prod (Word 5) (Word 1)) (Ty.Prod (Word 1) (Word 5)) (@full_left_shift1 (Word 1) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 1) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_32_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_32_4 (Ty.Prod (Word 5) (Word 2)) (Ty.Prod (Word 2) (Word 5)) (@full_left_shift1 (Word 2) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 2) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_32_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_32_8 (Ty.Prod (Word 5) (Word 3)) (Ty.Prod (Word 3) (Word 5)) (@full_left_shift1 (Word 3) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 8 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 3) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_32_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_32_16 (Ty.Prod (Word 5) (Word 4)) (Ty.Prod (Word 4) (Word 5)) (@full_left_shift1 (Word 4) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 16 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 4) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_8_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_8_1 (Ty.Prod (Word 0) (Word 3)) (Ty.Prod (Word 3) (Word 0)) (@full_right_shift1 (Word 0) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 0) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_8_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_8_2 (Ty.Prod (Word 1) (Word 3)) (Ty.Prod (Word 3) (Word 1)) (@full_right_shift1 (Word 1) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 1) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_8_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_8_4 (Ty.Prod (Word 2) (Word 3)) (Ty.Prod (Word 3) (Word 2)) (@full_right_shift1 (Word 2) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 8 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 8 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 2) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_16_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_16_1 (Ty.Prod (Word 0) (Word 4)) (Ty.Prod (Word 4) (Word 0)) (@full_right_shift1 (Word 0) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 0) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_16_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_16_2 (Ty.Prod (Word 1) (Word 4)) (Ty.Prod (Word 4) (Word 1)) (@full_right_shift1 (Word 1) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 1) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_16_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_16_4 (Ty.Prod (Word 2) (Word 4)) (Ty.Prod (Word 4) (Word 2)) (@full_right_shift1 (Word 2) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 2) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_16_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_16_8 (Ty.Prod (Word 3) (Word 4)) (Ty.Prod (Word 4) (Word 3)) (@full_right_shift1 (Word 3) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 16 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 16 8 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 3) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_32_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_32_1 (Ty.Prod (Word 0) (Word 5)) (Ty.Prod (Word 5) (Word 0)) (@full_right_shift1 (Word 0) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 1 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 0) 5 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_32_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_32_2 (Ty.Prod (Word 1) (Word 5)) (Ty.Prod (Word 5) (Word 1)) (@full_right_shift1 (Word 1) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 2 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 1) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_32_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_32_4 (Ty.Prod (Word 2) (Word 5)) (Ty.Prod (Word 5) (Word 2)) (@full_right_shift1 (Word 2) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 4 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 2) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_32_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_32_8 (Ty.Prod (Word 3) (Word 5)) (Ty.Prod (Word 5) (Word 3)) (@full_right_shift1 (Word 3) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 8 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 3) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_32_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_32_16 (Ty.Prod (Word 4) (Word 5)) (Ty.Prod (Word 5) (Word 4)) (@full_right_shift1 (Word 4) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e with (arg := fullshift_arg 32 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 32 16 ltac:(lia) ltac:(lia)).
  - split; vm_compute; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 4) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.
