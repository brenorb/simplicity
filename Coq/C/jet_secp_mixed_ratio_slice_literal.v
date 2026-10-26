(** Whole original indexed-ratio mixed call against the unchanged literal
    extended program on arbitrary matching bounded limbs. The output ratio
    is compared to the normalized literal projection; no raw public-jet
    equivalence is claimed. The C flag/Z invariant is also established. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_sx_mem C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_mixed_function_ratio_slice C.jet_secp_mixed_body_loose
 C.jet_secp_mixed_body_ratio_slice C.jet_secp_mixed_xy_ratio_literal C.jet_secp_mixed_xy_flag
 C.jet_secp_field_zero_owned C.jet_secp_rescale_literal C.jet_secp_add_literal
 C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_ge_add_ex canonical_fe_normalize.

Theorem eval_mixed_ratio_slice_literal x y z u v (ax ay az bx byword:Ty.tySem (Word 8)) m bp ba br base size :
 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned -> NoDup [bp;ba;br] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (field_zero_result z)) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m br 0 size Cur Freeable -> exists mf ox oy oz ratio,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
  [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br (Ptrofs.repr base)] E0 mf Vundef /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 fe_at mf br base (words5 ratio) /\ Mem.load Mint32 mf bp 120=Some (Vint (field_zero_result oz)) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\ square_input_bounds ratio /\
 (rescale_field_output ratio,((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz))=
 (@canonical_fe_normalize Alg.CoreFunSem (fst (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))),
  snd (@literal_gej_ge_add_ex Alg.CoreFunSem (((ax,ay),az),(bx,byword)))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\ Mem.range_perm mf br 0 size Cur Freeable /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 keeps_permissions m mf /\ lframe (fun b pos=>b<>bp /\ b<>ba /\ (b<>br \/ pos<base \/ base+40<=pos)) m mf /\
 readonly_preserved m mf.
Proof.
 intros Base Align Fit Max Distinct BX BY BZ BU BV HX HY HZ HU HV FlagA FlagB X Y Z U V FreeP FreeA FreeR.
 destruct (eval_mixed_ratio_slice_mode true x y z u v (field_zero_result z) m bp ba br base size Base Align Fit Max
   Distinct BX BY BZ BU BV FlagA FlagB X Y Z U V FreeP FreeA FreeR)
  as (mf & Call & XO & YO & ZO & FlagO & FreePO & FreeAO & BXO & BYO & BZO & Ratio & FreeRO &
    UO & VO & FlagBO & BRatio & Keep & Frame & Readonly).
 assert (FlagF:Mem.load Mint32 mf bp 120=Some (Vint
   (field_zero_result (mixed_mode_body_z_words true (field_zero_result z) x y z u v)))).
 { rewrite <- (mixed_xy_flag_preserved x y z u v (field_zero_result z) BX BY BZ BU BV eq_refl);exact FlagO. }
 pose proof (mixed_xy_ex_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV) as Literal.
 cbv zeta in Literal;rewrite <- (mixed_flag_of_residue z az HZ) in Literal.
 exists mf,(mixed_mode_body_x_words true (field_zero_result z) x y z u v),
  (mixed_mode_body_y_words true (field_zero_result z) x y z u v),
  (mixed_mode_body_z_words true (field_zero_result z) x y z u v),
  (mixed_mode_slice_ratio_words true (field_zero_result z) x y z u v).
 repeat (first [assumption|split]).
Qed.
