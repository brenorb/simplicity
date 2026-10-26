(** Complete original C coordinate scaling against the literal Simplicity
    zinv program. The C cube multiplies square(zi) by zi in that order;
    the residue proof connects it to the program without changing either. *)
From Coq Require Import ZArith List Ring.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_zinv_factor C.jet_secp_ge_zinv_arithmetic C.jet_secp_ge_zinv_function
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_separate_numeric C.jet_secp_point_mul_storage
 C.jet_secp_point_mul_numeric C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_literal_spec C.jet_secp_square_spec_bridge
 C.jet_secp_negate_literal_contract C.jet_secp_square_execution
 C.jet_secp_rescale_literal C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words rescale_field_output literal_fe_multiply literal_fe_square.

Lemma ge_zinv_words_literal x y zi (a b s:Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
 radix_value x mod field_prime=@toZ (WordToZ 8) a mod field_prime ->
 radix_value y mod field_prime=@toZ (WordToZ 8) b mod field_prime ->
 radix_value zi mod field_prime=@toZ (WordToZ 8) s mod field_prime ->
 (rescale_field_output (ge_zinv_x_words x zi),rescale_field_output (ge_zinv_y_words y zi))=
  @literal_gej_zinv Alg.CoreFunSem ((a,b),s).
Proof.
 intros BX BY BZI VX VY VZI.
 pose proof (square_result_reusable zi BZI) as BS.
 pose proof (rescale_square_writer zi s BZI VZI) as Square.
 assert (SquareResidue:radix_value (square_words zi) mod field_prime=
   @toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem s) mod field_prime).
 { rewrite <-Square,rescale_field_output_value,Z.mod_mod by (unfold field_prime,field_c;discriminate);reflexivity. }
 pose proof (rescale_mul_writer (square_words zi) zi (@literal_fe_square Alg.CoreFunSem s) s BS BZI SquareResidue VZI) as Cube.
 assert (CubeOrder:@literal_fe_multiply Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem s,s)=
   @literal_fe_cube Alg.CoreFunSem s).
 { apply (toZ_injective (WordToZ 8)).
   change (@toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem s,s))=
     @toZ (WordToZ 8) (@literal_fe_multiply Alg.CoreFunSem (s,@literal_fe_square Alg.CoreFunSem s))).
   rewrite !literal_multiply_numeric;f_equal;ring. }
 rewrite CubeOrder in Cube.
 assert (CubeResidue:radix_value (point_mul_words (square_words zi) zi) mod field_prime=
   @toZ (WordToZ 8) (@literal_fe_cube Alg.CoreFunSem s) mod field_prime).
 { rewrite <-Cube,rescale_field_output_value,Z.mod_mod by (unfold field_prime,field_c;discriminate);reflexivity. }
 pose proof (proj2 (point_mul_value_and_bounds (square_words zi) zi BS BZI)) as BC.
 pose proof (rescale_mul_writer x (square_words zi) a (@literal_fe_square Alg.CoreFunSem s)
   BX BS VX SquareResidue) as XOut.
 pose proof (rescale_mul_writer y (point_mul_words (square_words zi) zi) b (@literal_fe_cube Alg.CoreFunSem s)
   BY BC VY CubeResidue) as YOut.
 change ((rescale_field_output (point_mul_words x (square_words zi)),
   rescale_field_output (point_mul_words y (point_mul_words (square_words zi) zi)))=
   (@literal_fe_multiply Alg.CoreFunSem (a,@literal_fe_square Alg.CoreFunSem s),
    @literal_fe_multiply Alg.CoreFunSem (b,@literal_fe_cube Alg.CoreFunSem s))).
 rewrite XOut,YOut;reflexivity.
Qed.

Theorem eval_ge_set_gej_zinv_literal point size x y zi (a b s:Ty.tySem (Word 8)) m br ba bf flag :
 88<=size -> size<=Ptrofs.max_unsigned -> br<>ba -> br<>bf -> ba<>bf ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
 radix_value x mod field_prime=@toZ (WordToZ 8) a mod field_prime ->
 radix_value y mod field_prime=@toZ (WordToZ 8) b mod field_prime ->
 radix_value zi mod field_prime=@toZ (WordToZ 8) s mod field_prime ->
 Mem.load Mint32 m ba 120=Some (Vint flag) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
 fe_at m bf (ge_zinv_factor_offset point) (words5 zi) ->
 Mem.range_perm m br 0 size Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 (ge_zinv_factor_size point) Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_zinv)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef /\
 fe_at mf br 0 (words5 (ge_zinv_x_words x zi)) /\ fe_at mf br 40 (words5 (ge_zinv_y_words y zi)) /\
 (rescale_field_output (ge_zinv_x_words x zi),rescale_field_output (ge_zinv_y_words y zi))=
  @literal_gej_zinv Alg.CoreFunSem ((a,b),s) /\
 Mem.load Mint32 mf br 80=Some (Vint flag) /\ Mem.load Mint32 mf ba 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 square_input_bounds (ge_zinv_x_words x zi) /\ square_input_bounds (ge_zinv_y_words y zi) /\
 lframe (ge_zinv_frame br ba bf) m mf /\ readonly_preserved m mf.
Proof.
 intros Size Max RA RB AB BX BY BZI VX VY VZI Flag X Y Factor RF AF FF.
 destruct (eval_ge_set_gej_zinv point size x y zi m br ba bf flag
   Size Max RA RB AB BX BY BZI Flag X Y Factor RF AF FF)
  as (mf & Call & RX & RY & RFlag & AFlag & AX & AY & ZF & RFF & AFF & FFF & BXF & BYF & Frame & Readonly).
 exists mf;split;[exact Call|];split;[exact RX|];split;[exact RY|];
  split;[exact (ge_zinv_words_literal x y zi a b s BX BY BZI VX VY VZI)|];
  split;[exact RFlag|];split;[exact AFlag|];split;[exact AX|];split;[exact AY|];split;[exact ZF|];
  split;[exact RFF|];split;[exact AFF|];split;[exact FFF|];split;[exact BXF|];split;[exact BYF|];split;assumption.
Qed.
