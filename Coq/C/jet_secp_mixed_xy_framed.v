(** Original mixed addition with the flag and memory facts needed by the next
    Strauss iteration. All are derived from the existing full helper proof. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_field_zero_owned
 C.jet_secp_mixed_function_loose C.jet_secp_mixed_body_loose C.jet_secp_mixed_xy_literal
 C.jet_secp_mixed_xy_flag C.jet_secp_add_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_ge_add.
Set Default Timeout 10.

Theorem eval_mixed_xy_literal_framed x y z u v (ax ay az bx byword:Ty.tySem (Word 8)) m bp ba :
 bp<>ba -> square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value u mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value v mod feP=@toZ (WordToZ 8) byword mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
  [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),(bx,byword)) /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>bp /\ b<>ba) m mf.
Proof.
 intros Separate BX BY BZ BU BV HX HY HZ HU HV FlagA FlagB X Y Z U V FreeP FreeA.
 pose (flag:=bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))).
 destruct (eval_mixed_function_xy x y z u v flag m bp ba Separate BX BY BZ BU BV
  FlagA FlagB X Y Z U V FreeP FreeA)
  as (mf & Call & XO & YO & ZO & FlagO & FreePO & FreeAO & BXO & BYO & BZO & Frame).
 assert (Consistent:flag=field_zero_result z) by (symmetry;apply mixed_flag_of_residue;exact HZ).
 rewrite (mixed_xy_flag_preserved x y z u v flag BX BY BZ BU BV Consistent) in FlagO.
 rewrite (mixed_flag_of_residue _ _ (mixed_xy_output_residue _)) in FlagO.
 pose proof (mixed_xy_outputs_literal x y z u v ax ay az bx byword BX BY BZ BU BV HX HY HZ HU HV) as Literal.
 exists mf,(mixed_mode_body_x_words true flag x y z u v),
  (mixed_mode_body_y_words true flag x y z u v),(mixed_mode_body_z_words true flag x y z u v).
 split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
 split;[exact FreePO|];split;[exact FreeAO|];split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];
 split;[exact Literal|];split.
 - eapply secp_internal_keeps_permissions;[exact mixed_function_closed|reflexivity|exact Call].
 - split;[eapply mixed_function_readonly;exact Call|exact Frame].
Qed.
