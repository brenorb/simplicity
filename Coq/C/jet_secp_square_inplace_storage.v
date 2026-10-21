(** In-place square on actual owned field storage; reuse the selected square
    execution, output decoding and tight bounds, with no scratch copy call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_square_execution C.jet_secp_square_numeric_call C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_square_separate_numeric C.jet_secp_square_separate_caller
  C.jet_secp_curve_frame C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Theorem eval_square_inplace_from_storage rho m b :
  square_input_bounds rho -> fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (square_words rho)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  radix_value (square_words rho) mod field_prime = (radix_value rho*radix_value rho) mod field_prime /\
  square_input_bounds (square_words rho) /\
  (forall i, (i<5)%nat -> 0<=Int64.unsigned (square_words rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HB HI HF.
  assert (HR : rep rho [(b,0)] square_regs m).
  { apply (rep_add rho [] [] m b 0);[apply rep_nil|cbn;tauto|].
    apply field_words_region;[reflexivity|exact HI|exact HF]. }
  destruct (eval_original_square_owned_numeric rho [(b,0)] m HB HR)
    as (mf & HC & HP & HW & HV & HBounds & HL).
  destruct (square_output_region_field rho [(b,0)] mf 0 HB
    (rep_region _ _ _ mf 0 _ HP eq_refl)) as [FO FF].
  exists mf;split;[exact HC|]. split;[exact FO|]. split;[exact FF|].
  split;[exact HV|]. split;[apply square_result_reusable;exact HB|].
  split;[exact HBounds|]. exact (curve_frame_one square_regs b m mf eq_refl HL).
Qed.
