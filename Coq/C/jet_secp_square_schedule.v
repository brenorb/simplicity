(** Closed syntax comparison with the original optimized squaring execution. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Ctypes.
Require Import C.jet_sx_expr C.jet_secp_multiply_checkpoint_ops.
Require Import C.jet_secp_square_execution.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition doubled x := XLb Bmul x (XI2L Signed (XIc (Int.repr 2))).
Definition mask := XLc (Int64.repr 4503599627370495).
Definition red := XLc (Int64.repr 68719492368).
Definition masked (s : sx * sx) := XLb Band (fst s) mask.

Definition sq_c8 := sx_product (XLv 4) (XLv 4).
Definition sq_d3 := sx_accum (sx_product (doubled (XLv 0)) (XLv 3))
  (doubled (XLv 1)) (XLv 2).
Definition sq_fold3 := sx_accum sq_d3 red (fst sq_c8).
Definition sq_t3 := masked sq_fold3.
Definition sq_c8_hi := sx_shift64 sq_c8.
Definition sq_d3_hi := sx_shift52 sq_fold3.
Definition sq_d4 := sx_accum
  (sx_accum (sx_accum sq_d3_hi (XLv 0) (doubled (XLv 4)))
    (doubled (XLv 1)) (XLv 3)) (XLv 2) (XLv 2).
Definition sq_fold4 := sx_accum sq_d4 (XLsh Hshl red 12) (fst sq_c8_hi).
Definition sq_d4_hi := sx_shift52 sq_fold4.
Definition sq_tx := XLsh Hshr (masked sq_fold4) 48.
Definition sq_t4 := XLb Band (masked sq_fold4) (XLsh Hshru mask 4).

Definition sq_d5 := sx_accum (sx_accum sq_d4_hi (XLv 1) (doubled (XLv 4)))
  (doubled (XLv 2)) (XLv 3).
Definition sq_u0 := XLb Bor (XLsh Hshl (masked sq_d5) 4) sq_tx.
Definition sq_c0 := sx_accum (sx_product (XLv 0) (XLv 0)) sq_u0 (XLsh Hshru red 4).
Definition sq_r0 := masked sq_c0.
Definition sq_c0_hi := sx_shift52 sq_c0.
Definition sq_d5_hi := sx_shift52 sq_d5.

Definition sq_c1 := sx_accum sq_c0_hi (doubled (XLv 0)) (XLv 1).
Definition sq_d6 := sx_accum (sx_accum sq_d5_hi (XLv 2) (doubled (XLv 4))) (XLv 3) (XLv 3).
Definition sq_fold1 := sx_accum sq_c1 (masked sq_d6) red.
Definition sq_r1 := masked sq_fold1.
Definition sq_c1_hi := sx_shift52 sq_fold1.
Definition sq_d6_hi := sx_shift52 sq_d6.

Definition sq_c2 := sx_accum (sx_accum sq_c1_hi (doubled (XLv 0)) (XLv 2)) (XLv 1) (XLv 1).
Definition sq_d7 := sx_accum sq_d6_hi (XLv 3) (doubled (XLv 4)).
Definition sq_fold2 := sx_accum sq_c2 red (fst sq_d7).
Definition sq_r2 := masked sq_fold2.
Definition sq_c2_hi := sx_shift52 sq_fold2.
Definition sq_d7_hi := sx_shift64 sq_d7.
Definition sq_c3 := sx_accum_word (sx_accum sq_c2_hi (XLsh Hshl red 12) (fst sq_d7_hi)) sq_t3.
Definition sq_r3 := masked sq_c3.
Definition sq_r4 := XLb Badd (fst (sx_shift52 sq_c3)) sq_t4.
