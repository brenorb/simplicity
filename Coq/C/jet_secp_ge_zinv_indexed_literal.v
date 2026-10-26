(** Whole indexed original ge_set_gej_zinv against the existing literal zinv.
    Preserve all previously proved source, factor, ownership and frame facts. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_zinv_factor C.jet_secp_ge_zinv_arithmetic C.jet_secp_ge_zinv_literal
 C.jet_secp_ge_zinv_indexed_function C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_rescale_literal C.jet_clight_internal_preserve.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output.

Theorem eval_ge_set_gej_zinv_indexed_literal point base size x y zi (a b s:Ty.tySem (Word 8)) m br ba bf flag :
 0<=base -> (8|base) -> base+88<=size -> size<=Ptrofs.max_unsigned -> br<>ba -> br<>bf -> ba<>bf ->
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
  [Vptr br (Ptrofs.repr base);Vptr ba Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef /\
 fe_at mf br (base+0) (words5 (ge_zinv_x_words x zi)) /\ fe_at mf br (base+40) (words5 (ge_zinv_y_words y zi)) /\
 (rescale_field_output (ge_zinv_x_words x zi),rescale_field_output (ge_zinv_y_words y zi))=
  @literal_gej_zinv Alg.CoreFunSem ((a,b),s) /\
 Mem.load Mint32 mf br (base+80)=Some (Vint flag) /\ Mem.load Mint32 mf ba 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf br 0 size Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 square_input_bounds (ge_zinv_x_words x zi) /\ square_input_bounds (ge_zinv_y_words y zi) /\
 lframe (ge_zinv_indexed_frame br base ba bf) m mf /\ readonly_preserved m mf.
Proof.
 intros Base Align Fit Max RA RB AB BX BY BZI VX VY VZI Flag X Y Factor RF AF FF.
 destruct (eval_ge_set_gej_zinv_indexed point base size x y zi m br ba bf flag
   Base Align Fit Max RA RB AB BX BY BZI Flag X Y Factor RF AF FF)
  as (mf & Call & RX & RY & RFlag & AFlag & AX & AY & ZF & RFF & AFF & FFF & BXF & BYF & Frame & Readonly).
 exists mf;split;[exact Call|];split;[exact RX|];split;[exact RY|];
  split;[exact (ge_zinv_words_literal x y zi a b s BX BY BZI VX VY VZI)|];
  split;[exact RFlag|];split;[exact AFlag|];split;[exact AX|];split;[exact AY|];split;[exact ZF|];
  split;[exact RFF|];split;[exact AFF|];split;[exact FFF|];split;[exact BXF|];split;[exact BYF|];split;assumption.
Qed.
