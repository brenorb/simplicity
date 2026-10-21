(** The original finite-affine C helper returns the literal canonical curve bit.
    This is its specification bridge; the public reader/writer wrapper remains
    a separate obligation. No input word is assumed canonical or on the curve. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_point_three_reads.
Require Import C.jet_secp_square_columns C.jet_secp_square_spec_bridge.
Require Import C.jet_secp_rescale_literal C.jet_secp_rescale_public_reads.
Require Import C.jet_secp_curve_body C.jet_secp_curve_function C.jet_secp_curve_literal.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_ge_is_on_curve secp_ge.

Lemma curve_reader_square_residue x :
  (radix_value (square_reader_rho x) * radix_value (square_reader_rho x)) mod feP =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod feP.
Proof.
  change ((radix_value (square_reader_rho x) * radix_value (square_reader_rho x)) mod field_prime =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod field_prime).
  rewrite Z.mul_mod, rescale_reader_residue, <- Z.mul_mod by (unfold field_prime,field_c; lia).
  reflexivity.
Qed.
Lemma curve_reader_cube_residue x :
  (radix_value (square_reader_rho x) * radix_value (square_reader_rho x) *
    radix_value (square_reader_rho x) + 7) mod feP =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x + 7) mod feP.
Proof.
  rewrite Z.add_mod, Z.mul_mod by (unfold feP,feR; lia).
  rewrite curve_reader_square_residue.
  change ((((@toZ (WordToZ 8) x * @toZ (WordToZ 8) x) mod field_prime *
    (radix_value (square_reader_rho x) mod field_prime)) mod field_prime +
    7 mod field_prime) mod field_prime =
    (@toZ (WordToZ 8) x * @toZ (WordToZ 8) x * @toZ (WordToZ 8) x + 7) mod field_prime).
  rewrite rescale_reader_residue, <- Z.mul_mod, <- Z.add_mod by (unfold field_prime,field_c; lia).
  reflexivity.
Qed.
Lemma curve_result_matches_literal x y :
  curve_result (square_reader_rho x) (square_reader_rho y) =
    bit_int (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))).
Proof.
  unfold curve_result, bit_int. rewrite literal_ge_curve_numeric,
    curve_reader_square_residue, curve_reader_cube_residue. reflexivity.
Qed.

Theorem eval_curve_finite_literal x y m ba :
  fe_at m ba 0 (point_canonical_limbs x) -> fe_at m ba 40 (point_canonical_limbs y) ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
      [Vptr ba Ptrofs.zero] E0 mf
      (Vint (bit_int (Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))))) /\
    fe_at mf ba 0 (point_canonical_limbs x) /\ fe_at mf ba 40 (point_canonical_limbs y) /\
    Mem.range_perm mf ba 0 88 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  rewrite !rescale_reader_limbs. intros HX HY HF HFlag.
  destruct (eval_curve_finite_function (square_reader_rho x) (square_reader_rho y) m ba
    (square_reader_bounds x) (square_reader_bounds y) HX HY HF HFlag)
    as (mf & HC & HXF & HYF & HFF & HFrame).
  rewrite curve_result_matches_literal in HC.
  exists mf. split; [exact HC|]. split; [exact HXF|]. split; [exact HYF|]. split; assumption.
Qed.
Print Assumptions curve_result_matches_literal.
Print Assumptions eval_curve_finite_literal.
