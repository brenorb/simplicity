(** Actual original C helper call to literal Simplicity, at an arbitrary represented inverse-Z. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_set_bit
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_add_literal
 C.jet_secp_zinv_finite C.jet_secp_zinv_function C.jet_secp_zinv_function_infinite
 C.jet_secp_zinv_infinite_products C.jet_secp_zinv_literal_outputs C.jet_secp_zinv_one_numeric
 C.jet_secp_zinv_differences C.jet_secp_curve_literal C.jet_secp_square_execution.
Require Import C.jet_secp_zinv_flag.
Import ListNotations Values.
Require Import C.jet_secp_zinv_general_numeric C.jet_secp_zinv_general_outputs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words rescale_field_output literal_gej_ge_add canonical_fe_is_zero.

Theorem eval_zinv_scaled_literal x y z u v inv (ax ay az bx byword s : Ty.tySem (Word 8)) m bp ba bb :
 NoDup [bp;ba;bb] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_zinv_var)
   [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (if Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)
   then Int.zero else zinv_finite_flag x y z u v inv)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_gej_zinv Alg.CoreFunSem ((bx,byword),s)) /\
 lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros Sep BX BY BZ BU BV BI Scale HX HY HZ HU HV FlagA FlagB X Y ZAt U V Inv PF AF InvF.
 unfold bit_int in FlagA.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:HInf.
 - destruct (eval_zinv_function_infinite u v inv Int.one Int.zero m bp ba bb Sep ltac:(discriminate)
     BU BV BI FlagA FlagB U V Inv PF AF InvF)
     as (mf & Call & XO & YO & ZO & FlagO & UO & VO & InvO & PFO & AFO & InvFO & BXO & BYO & BZO & Frame).
   pose proof (zinv_infinite_outputs_scaled_literal u v inv ax ay az bx byword s BU BV BI Scale HU HV HInf) as Literal.
   assert (FlagLiteral : Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output (point_set_bit_words true))))))).
   { rewrite literal_curve_zero_numeric,rescale_field_output_value,field_prime_matches_normalizer.
     change (Mem.load Mint32 mf bp 120=Some (Vint Int.zero));exact FlagO. }
   exists mf,(point_mul_words u (square_words inv)),(point_mul_words v (zinv_inverse_cube inv)),(point_set_bit_words true).
   repeat first [assumption|split].
 - destruct (eval_zinv_function_finite x y z u v inv m bp ba bb Sep BX BY BZ BU BV BI FlagA FlagB
     X Y ZAt U V Inv PF AF InvF)
     as (mf & Call & XO & YO & ZO & FlagO & UO & VO & InvO & PFO & AFO & InvFO & BXO & BYO & BZO & Frame).
   pose proof (zinv_finite_outputs_scaled_literal x y z u v inv ax ay az bx byword s
     BX BY BZ BU BV BI Scale HX HY HZ HU HV HInf) as Literal.
   assert (BH : square_input_bounds (zinv_h_words x z u inv)).
   { exact (proj1 (proj2 (proj2 (zinv_differences_value x y z u v inv
       ltac:(intros j HJ;pose proof (square_input56 x BX j HJ);lia)
       ltac:(intros j HJ;pose proof (square_input56 y BY j HJ);lia) BZ BU BV BI)))). }
   assert (NZ : radix_value z mod feP<>0).
   { rewrite HZ;rewrite literal_curve_zero_numeric in HInf;apply Z.eqb_neq;exact HInf. }
   assert (FlagLiteral : Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output (zinv_finite_z x y z u v inv))))))).
   { rewrite literal_curve_zero_numeric,rescale_field_output_value,field_prime_matches_normalizer,
       Z.mod_mod by (unfold feP,feR;lia).
     rewrite <-(zinv_finite_flag_consistent x y z u v inv BZ BH NZ);exact FlagO. }
   exists mf,(zinv_finite_x x y z u v inv),(zinv_finite_y x y z u v inv),(zinv_finite_z x y z u v inv).
   repeat first [assumption|split].
Qed.
