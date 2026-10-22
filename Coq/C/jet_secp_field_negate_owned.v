(** Reuse original in-place magnitude-one negation on arbitrary tight owned
    limbs, including the 49-bit top limb returned by multiplication/squaring. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_rep C.jet_sx_state C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_field_mul_small C.jet_secp_field_negate_storage C.jet_secp_field_negate_separate
  C.jet_secp_curve_weak C.jet_secp_field_weak_tight C.jet_secp_curve_frame C.jet_secp_local_regions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem eval_inplace_negate_tight_owned w m b :
  mul_small_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero;Vint Int.one] E0 mf Vundef /\
  fe_at mf b 0 (words5 (negate_sep_words w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (negate_sep_words w)=4*feP-radix_value w /\ square_input_bounds (negate_sep_words w) /\
  lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros BW HF HP.
  assert (HR : rep (weak_shift_words w) [(b,0)] local_write_initial_regs m).
  { apply curve_weak_initial_rep;[rewrite weak_shift_values;exact HF|exact HP]. }
  destruct (eval_field_negate_to_field m b (weak_shift_words w) HR) as (mf & HC & HO & HFree & HL).
  change (fe_at mf b 0 (words5 (negate_sep_words w))) in HO.
  destruct (negate_sep_numeric w BW) as [HV HB].
  exists mf;split;[exact HC|];split;[exact HO|];split;[exact HFree|];split;[exact HV|];split;[exact HB|].
  apply curve_frame_one with (regs:=local_write_initial_regs);[reflexivity|exact HL].
Qed.
