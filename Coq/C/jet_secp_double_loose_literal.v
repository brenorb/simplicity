(** Original in-place doubling on arbitrary matching loose coordinates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_execution C.jet_secp_double_all_calls
 C.jet_secp_double_var_owned C.jet_secp_double_literal C.jet_secp_double_literal_bridge
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate
 C.jet_secp_literal_infinity C.jet_secp_curve_literal.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output canonical_fe_is_zero literal_gej_double.

Lemma double_loose_outputs_literal x y z (ax ay az : Ty.tySem (Word 8)) :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 let flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) in
 ((rescale_field_output (double_var_x_words flag x y),rescale_field_output (double_var_y_words flag x y)),
   rescale_field_output (double_var_z_words flag y z))=
 @literal_gej_double Alg.CoreFunSem ((ax,ay),az).
Proof.
 intros BX BY BZ HX HY HZ;cbn zeta.
 rewrite literal_gej_double_step,literal_gej_is_infinity_value.
 unfold bit_int,double_var_x_words,double_var_y_words,double_var_z_words.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)).
 - change (((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
     rescale_field_output (fun _ : nat=>Int64.zero))=
     ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
   assert (Zero : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
     by exact zero_field_writer_literal_output.
   rewrite Zero;reflexivity.
 - change (((rescale_field_output (double_output_x_words x y),rescale_field_output (double_output_y_words x y)),
     rescale_field_output (double_output_z_words y z))=@literal_gej_double_body Alg.CoreFunSem ((ax,ay),az)).
   exact (double_body_writer_outputs_literal x y z ax ay az BX BY BZ HX HY HZ).
Qed.

Lemma double_var_output_flag_consistent flag y z :
 double_var_output_flag flag y z=
 bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem
   (rescale_field_output (double_var_z_words flag y z)))).
Proof.
 rewrite literal_curve_zero_numeric,rescale_field_output_value,field_prime_matches_normalizer,
   Z.mod_mod by (unfold feP,feR;lia).
 unfold double_var_output_flag,double_var_z_words.
 destruct (Int.eq flag Int.zero).
 - reflexivity.
 - reflexivity.
Qed.

Theorem eval_double_var_loose_literal x y z (ax ay az : Ty.tySem (Word 8)) m bp :
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
   [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   @literal_gej_double Alg.CoreFunSem ((ax,ay),az) /\ lframe (fun b _=>b<>bp) m mf.
Proof.
 intros BX BY BZ HX HY HZ Flag X Y ZAt Free.
 set (flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))) in *.
 destruct (eval_double_var_owned x y z m bp flag BX BY BZ Flag X Y ZAt Free)
   as (mf & Call & XO & YO & ZO & FlagO & FreeO & BXO & BYO & BZO & Frame).
 rewrite double_var_output_flag_consistent in FlagO.
 pose proof (double_loose_outputs_literal x y z ax ay az BX BY BZ HX HY HZ) as Literal.
 exists mf,(double_var_x_words flag x y),(double_var_y_words flag x y),(double_var_z_words flag y z).
 repeat first [assumption|split].
Qed.
