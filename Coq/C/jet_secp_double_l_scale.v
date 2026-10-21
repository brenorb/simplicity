(** The two real calls producing L from the squared X-coordinate in
    secp256k1_gej_double.  No inserted normalization or assumed call result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_field_mul_small C.jet_secp_field_half C.jet_secp_field_half_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_columns C.jet_secp_fe_math.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition double_l_words w := half_words (mul_small_words (Int.repr 3) w).

Theorem eval_double_l_scale w m b : mul_small_input_bounds w ->
  fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mm mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul_int)
    [Vptr b Ptrofs.zero;Vint (Int.repr 3)] E0 mm Vundef /\
  Clight2.eval_funcall secp_ge mm (Internal f_secp256k1_fe_half)
    [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (double_l_words w)) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  square_input_bounds (double_l_words w) /\
  2*radix_value (double_l_words w)=3*radix_value w+
    half_parity (mul_small_words (Int.repr 3) w)*feP /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HB HI HF.
  destruct (eval_field_mul_small_from_storage (Int.repr 3) w m b
    ltac:(change (0<=3<=7);lia) HB HI HF)
    as (mm & HM & HO & HFree & HValue & HBounds & HFrameM).
  destruct (eval_field_half_numeric (mul_small_words (Int.repr 3) w) mm b HBounds HO HFree)
    as (mf & HH & HOut & HFree' & HBounds' & HValue' & HFrameH).
  change (radix_value (mul_small_words (Int.repr 3) w)=3*radix_value w) in HValue.
  rewrite HValue in HValue'.
  exists mm,mf;split;[exact HM|];split;[exact HH|];split;[exact HOut|];
    split;[exact HFree'|];split;[exact HBounds'|];split;[exact HValue'|].
  eapply lframe_trans;[exact HFrameM|exact HFrameH].
Qed.
