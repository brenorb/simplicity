(** Full C-derived bit versus the fixed primitive-bearing equivalence program.
    All Word256 coordinates are allowed; no curve or canonical-input premise. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_multiply_finish_product
 C.jet_secp_square_spec_bridge C.jet_secp_mixed_finite_return
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero C.jet_secp_curve_literal
 C.jet_secp_mixed_dispatch_literal C.jet_secp_gej_ge_equiv_dispatch
 C.jet_secp_gej_ge_equiv_reader C.jet_secp_gej_ge_equiv_flag
 C.jet_secp_gej_ge_equiv_literal C.jet_secp_field_prime.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque gej_ge_equiv_reader_bit literal_gej_ge_equiv canonical_fe_is_zero canonical_fe_normalize.

Lemma equiv_finite_nonzero_h (x y z u v : Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=false ->
 Z.eqb (radix_value (mixed_h_words (square_reader_rho x) (square_reader_rho z)
  (square_reader_rho u)) mod feP) 0=false ->
 gej_ge_equiv_reader_bit x y z u v=
 Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))).
Proof.
 intros Fin HNonzero.
 destruct (equiv_finite_nonzero_h_reduction x y z u v Fin HNonzero) as [CBit SpecBit].
 rewrite CBit,SpecBit;symmetry;apply Z.eqb_neq.
 apply secp256k1_nonzero_negative_product.
 - rewrite equiv_negated_h_test,literal_curve_zero_numeric in HNonzero.
   apply Z.eqb_neq;exact HNonzero.
 - assert (NFin : Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
     (@canonical_fe_normalize Alg.CoreFunSem z))=false)
     by (rewrite equiv_normalized_zero_test;exact Fin).
   rewrite literal_curve_zero_numeric in NFin.
   apply Z.eqb_neq;exact NFin.
Qed.

Theorem gej_ge_equiv_reader_matches_literal (x y z u v : Ty.tySem (Word 8)) :
 gej_ge_equiv_reader_bit x y z u v=
 Bit.toBool (@literal_gej_ge_equiv Alg.CoreFunSem (((x,y),z),(u,v))).
Proof.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)) eqn:Inf.
 - apply equiv_incoming_infinity;exact Inf.
 - destruct (Z.eqb (radix_value (mixed_h_words (square_reader_rho x) (square_reader_rho z)
    (square_reader_rho u)) mod feP) 0) eqn:HZero.
   + apply equiv_finite_zero_h;assumption.
   + apply equiv_finite_nonzero_h;assumption.
Qed.
