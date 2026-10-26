(** Original distinct-source finite double_var against the existing literal
    Simplicity doubling term. The zero/nonzero-Z relation is the represented
    infinity flag, not an on-curve or nonzero-Y restriction. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product
 C.jet_secp_double_all_calls C.jet_secp_double_var_owned C.jet_secp_double_var_separate
 C.jet_secp_double_loose_literal C.jet_secp_double_literal_bridge C.jet_secp_double_literal
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output canonical_fe_is_zero literal_gej_double.

Theorem eval_double_var_separate_literal x y z (ax ay az:Ty.tySem (Word 8)) m br ba :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> br<>ba ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output (double_output_z_words y z)))))) /\
 ((rescale_field_output (double_output_x_words x y),rescale_field_output (double_output_y_words x y)),
   rescale_field_output (double_output_z_words y z))=@literal_gej_double Alg.CoreFunSem ((ax,ay),az) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (fun b pos=>(b<>br \/ pos<0 \/ 124<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos)) m mf /\
 readonly_preserved m mf.
Proof.
 intros BX BY BZ RA VX VY VZ Finite Flag X Y ZAt RF AF.
 destruct (eval_double_var_separate_finite x y z m br ba BX BY BZ RA Flag X Y ZAt RF AF)
  as (mf & Call & RXF & RYF & RZF & RFlag & AFlag & AXF & AYF & AZF &
      RFF & AFF & BXF & BYF & BZF & Frame & Readonly).
 pose proof (double_loose_outputs_literal x y z ax ay az BX BY BZ VX VY VZ) as Literal.
 rewrite Finite in Literal.
 change (((rescale_field_output (double_output_x_words x y),rescale_field_output (double_output_y_words x y)),
   rescale_field_output (double_output_z_words y z))=@literal_gej_double Alg.CoreFunSem ((ax,ay),az)) in Literal.
 pose proof (double_var_output_flag_consistent Int.zero y z) as FlagConsistent.
 change (double_var_zflag y z=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (rescale_field_output (double_output_z_words y z))))) in FlagConsistent.
 rewrite FlagConsistent in RFlag.
 exists mf;split;[exact Call|];split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];
  split;[exact RFlag|];split;[exact Literal|];split;[exact AFlag|];split;[exact AXF|];
  split;[exact AYF|];split;[exact AZF|];split;[exact RFF|];split;[exact AFF|];
  split;[exact BXF|];split;[exact BYF|];split;[exact BZF|];split;assumption.
Qed.
