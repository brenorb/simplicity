(** Retain the stored infinity flag through the actual final Z correction
    when the shared denominator is nonzero. The caller must derive that
    internal condition from its valid affine input, not assume it publicly. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_sx_mem C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_rescale_statements C.jet_secp_rescale_literal
 C.jet_secp_strauss_final_literal C.jet_secp_generator_final C.jet_secp_multiply_literal_spec
 C.jet_secp_curve_literal C.jet_secp_canonical_zero C.jet_secp_negate_literal_contract C.jet_secp_field_prime.
Import Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_fe_multiply canonical_fe_is_zero.

Lemma literal_zero_product_nonzero_factor (a b:Ty.tySem (Word 8)) :
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem b)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_multiply Alg.CoreFunSem (a,b)))=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem a).
Proof.
 intro Nonzero;rewrite !literal_curve_zero_numeric in *.
 rewrite literal_multiply_numeric,Z.mod_mod by (unfold feP,feR;lia).
 destruct (Z.eqb (@toZ (WordToZ 8) a mod feP) 0) eqn:Zero.
 - apply Z.eqb_eq in Zero;apply Z.eqb_eq.
   rewrite Z.mul_mod,Zero,Z.mul_0_l,Z.mod_0_l by (unfold feP,feR;lia);reflexivity.
 - apply Z.eqb_neq;apply secp256k1_nonzero_product;apply Z.eqb_neq;assumption.
Qed.

Theorem exec_strauss_final_flag x y z inv e le m bp bb :
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_fe_mul=None -> bp<>bb ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output inv))=false ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf oz,
 Clight2.exec_stmt secp_ge e le m generator_final_statement E0
  (PTree.set _t'16 (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) le) mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds oz /\
 rescale_field_output oz=@literal_fe_multiply Alg.CoreFunSem (rescale_field_output z,rescale_field_output inv) /\
 lframe (fun b _=>b<>bp /\ b<>bb) m mf.
Proof.
 intros R ZLocal MulSymbol Separate BX BY BZ BI Nonzero Flag X Y ZAt Inv FreeR FreeI.
 destruct (exec_strauss_final_literal x y z inv e le m bp bb R ZLocal MulSymbol Separate
  BX BY BZ BI Flag X Y ZAt Inv FreeR FreeI)
  as (mf & oz & Exec & XO & YO & ZO & FlagO & InvO & FreeRO & FreeIO & Bound & Literal & Frame).
 assert (FlagValue:Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))=
  Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))).
 { rewrite Literal;apply literal_zero_product_nonzero_factor;exact Nonzero. }
 exists mf,oz;rewrite FlagValue;repeat first [assumption|split].
Qed.
