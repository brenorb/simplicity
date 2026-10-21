(** Original complete projective C helper against the literal Simplicity
    program, for all three Word256 inputs.  No infinity-flag premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_normalize_bridge C.jet_secp_point_three_reads C.jet_secp_square_spec_bridge.
Require Import C.jet_secp_rescale_public_reads C.jet_secp_rescale_literal
  C.jet_secp_curve_literal C.jet_secp_curve_literal_bridge C.jet_secp_gej_curve_literal_numeric
  C.jet_secp_gej_curve_function.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_is_on_curve secp_ge.

Lemma curve_residue_mul a b c d :
  a mod feP=b mod feP -> c mod feP=d mod feP -> (a*c) mod feP=(b*d) mod feP.
Proof.
  intros HA HC;rewrite (Z.mul_mod a c feP),(Z.mul_mod b d feP),HA,HC
    by (unfold feP,feR;lia);reflexivity.
Qed.

Lemma gej_curve_reader_cube_residue x :
  (radix_value (square_reader_rho x)*radix_value (square_reader_rho x)*radix_value (square_reader_rho x)) mod feP=
  (@toZ (WordToZ 8) x*@toZ (WordToZ 8) x*@toZ (WordToZ 8) x) mod feP.
Proof.
  apply curve_residue_mul;[apply curve_reader_square_residue|apply rescale_reader_residue].
Qed.

Lemma gej_curve_reader_six_residue z :
  (radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*
   radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*radix_value (square_reader_rho z)) mod feP=
  (@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*
   @toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z) mod feP.
Proof.
  rewrite <- (gej_curve_six_mod (radix_value (square_reader_rho z))),
    <- (gej_curve_six_mod (@toZ (WordToZ 8) z)),gej_curve_reader_cube_residue;reflexivity.
Qed.

Lemma gej_curve_reader_polynomial x z :
  (radix_value (square_reader_rho x)*radix_value (square_reader_rho x)*radix_value (square_reader_rho x)+
   7*(radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*
      radix_value (square_reader_rho z)*radix_value (square_reader_rho z)*radix_value (square_reader_rho z))) mod feP=
  (@toZ (WordToZ 8) x*@toZ (WordToZ 8) x*@toZ (WordToZ 8) x+
   7*(@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z*
      @toZ (WordToZ 8) z*@toZ (WordToZ 8) z*@toZ (WordToZ 8) z)) mod feP.
Proof.
  rewrite (Z.add_mod _ _ feP),(Z.add_mod (_*_*_) _ feP),
    gej_curve_reader_cube_residue by (unfold feP,feR;lia).
  f_equal;f_equal;apply curve_residue_mul;[reflexivity|apply gej_curve_reader_six_residue].
Qed.

Lemma gej_curve_result_matches_literal x y z :
  gej_curve_result (square_reader_rho x) (square_reader_rho y) (square_reader_rho z)=
    bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))).
Proof.
  unfold gej_curve_result,bit_int;rewrite literal_gej_curve_numeric,
    curve_reader_square_residue,gej_curve_reader_polynomial;reflexivity.
Qed.

Theorem eval_gej_curve_literal x y z m ba :
  fe_at m ba 0 (point_canonical_limbs x) -> fe_at m ba 40 (point_canonical_limbs y) ->
  fe_at m ba 80 (point_canonical_limbs z) -> Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf
    (Vint (bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))))) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  rewrite !rescale_reader_limbs;intros HX HY HZ HF.
  destruct (eval_gej_curve_function (square_reader_rho x) (square_reader_rho y) (square_reader_rho z)
    m ba (square_reader_bounds x) (square_reader_bounds y) (square_reader_bounds z) HX HY HZ HF)
    as (mf & HC & HFree & HFrame).
  rewrite gej_curve_result_matches_literal in HC.
  exists mf;split;[exact HC|];split;assumption.
Qed.
