(** Whole original Strauss call for all point and scalar words.
    Both the finite and skipped contribution branches execute literally. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_strauss_point_loop C.jet_secp_strauss_digit_guard
 C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_wnaf5_literal C.jet_secp_strauss_wnaf_calls
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_double_loose_literal
 C.jet_secp_double_literal C.jet_secp_mixed_xy_literal C.jet_secp_strauss_program
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_double literal_strauss_step.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_scale_iteration.


Require Import C.jet_secp_strauss_scale_loop C.jet_secp_negate_literal_contract C.jet_secp_globalz_word_walk C.jet_secp_generator_point_stage C.jet_secp_generator_entry C.jet_secp_generator_final C.jet_secp_strauss_final_literal
 C.jet_secp_double_var_owned C.jet_secp_gej_infinity_owned C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_generator_loop_literal.
Local Opaque literal_fe_multiply literal_gej_infinity.

Require Import C.jet_clight_readonly_frame C.jet_secp_strauss_generator_zero C.jet_secp_strauss_digit_index C.jet_secp_strauss_scale_point_stage C.jet_secp_strauss_scale_literal
 C.jet_secp_strauss_zero_generator C.jet_secp_generator_main C.jet_secp_generator_digit_index
 C.jet_secp_strauss_complete_program C.jet_secp_split_literal C.jet_secp_wnaf5_input
 C.jet_secp_wnaf5_signed_array C.jet_secp_wnaf_loop C.jet_memset_model.
Local Opaque literal_strauss_body literal_scalar_table5 literal_scalar_split_lambda.



From Coq Require Import ZArith List.
From compcert Require Import Coqlib Memory Values.
Require Import C.jet_sx_mem C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_scale_function C.jet_secp_strauss_general_main C.jet_secp_generator_pair_general C.jet_secp_generator_globals.
Require Import C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_clight_readonly_frame C.jet_secp_strauss_beta_prepare
 C.jet_secp_strauss_first_loop C.jet_secp_generator_globalz_call C.jet_secp_generator_preprocess
 C.jet_secp_statement_prefix C.jet_secp_point_mul_storage C.jet_secp_field_zero_owned
 C.jet_secp_odd_table_body C.jet_secp_odd_table_loop C.jet_secp_double_all_calls
 C.jet_secp_strauss_scale_main C.jet_secp_beta_state C.jet_secp_beta_loop_step
 C.jet_secp_odd_table_literal_walk C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support C.jet_secp_generator_initialize
 C.jet_secp_generator_function C.jet_secp_split_function C.jet_secp_wnaf_slice_frame C.jet_secp_beta_loop.

Require Import C.jet_secp_strauss_general_finite C.jet_secp_strauss_general_skipped
 C.jet_secp_literal_gej_predicate C.jet_secp_canonical_scalar_zero
 C.jet_secp_generate_program C.jet_predicate_spec C.jet_secp_mixed_xy_flag.
Local Opaque literal_off_curve_linear_combination_1 literal_strauss_guard literal_generate.

Theorem eval_strauss_general (Model:memset_model)
 (raw ng ax ay az:Ty.tySem (Word 8)) x y z m br bk ba bs bp bt bx bng :
 (forall h,generator_table_state h m) -> split_constants_ready m -> beta_initialized m ->
 NoDup [br;bk;ba;bs;bp;bt;bx;bng] ->
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az))))) ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf ox oy oz,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_off_curve_linear_combination_1 Alg.CoreFunSem ((raw,((ax,ay),az)),ng) /\
 (forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>~In b [br;bk;ba;bs;bp;bt;bx;bng]) m mf.
Proof.
 intros Tables Ready Beta Separate Owned Input InputNG BX BY BZ X Y Z Flag HX HY HZ PS PT PX.
 destruct (Bit.toBool (@literal_strauss_guard Alg.CoreFunSem
  ((raw,((ax,ay),az)),ng))) eqn:Guard.
 - assert (Skip:
   @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)=0 \/
   Mem.load Mint32 m ba 120=Some (Vint Int.one)).
   { rewrite literal_strauss_guard_value in Guard;apply Bool.orb_true_iff in Guard.
     destruct Guard as [Infinity|Zero].
     - right;unfold bit_int in Flag;rewrite Infinity in Flag;exact Flag.
     - left;apply Z.eqb_eq;rewrite canonical_scalar_zero_after_normalize;exact Zero. }
   assert (Different:br<>bng).
   { intro Same;subst bng;apply (NoDup_cons_iff _ _) in Separate.
     apply (proj1 Separate);clear;cbn [In];tauto. }
   destruct (eval_strauss_general_skipped Model
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)) ng
    m br bk ba bs bt bx bng Tables
    ltac:(change (0<=@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<word_modulus 8);apply word_value_bounds)
    Input Skip PT PX InputNG Different
    (Owned br 128 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto))
    (Owned bng 32 ltac:(clear;cbn [strauss_linear_outer_storage In];tauto)))
    as (mf & ox & oy & oz & Call & XO & YO & ZO & BXO & BYO & BZO & Literal & FreeR & FreeNG & TablesF & Frame).
   assert (OwnedF:forall b hi,In (b,hi) (strauss_linear_outer_storage br bk ba bs bp bt bx bng) ->
    Mem.range_perm mf b 0 hi Cur Freeable).
   { intros b hi Slot;destruct (Pos.eq_dec b br) as [Same|Other].
     - subst b;assert (Size:hi=128).
       { clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate.
         cbn [strauss_linear_outer_storage In] in Slot;intuition congruence. }
       subst hi;exact FreeR.
     - destruct (Pos.eq_dec b bng) as [Same|OtherNG].
       + subst b;assert (Size:hi=32).
         { clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate.
           cbn [strauss_linear_outer_storage In] in Slot;intuition congruence. }
         subst hi;exact FreeNG.
       + eapply curve_keep_free;[eapply strauss_linear_outer_size_positive;exact Slot|
          exact (Owned b hi Slot)|exact Frame|intros;split;assumption]. }
   exists mf,ox,oy,oz;
    split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];
    split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
   + rewrite literal_off_curve_linear_combination_1_value.
     change (((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
       if Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,((ax,ay),az)),ng))
       then @literal_generate Alg.CoreFunSem ng
       else @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),ng)).
     rewrite Guard;exact Literal.
   + split;[exact OwnedF|];split;[exact TablesF|].
     eapply lframe_implies;[exact Frame|].
     intros b pos Outside Valid;clear -Outside;cbn [In] in Outside|-*;intuition congruence.
 - pose proof Guard as Parts;rewrite literal_strauss_guard_value in Parts;
    apply Bool.orb_false_iff in Parts;destruct Parts as [Infinity Zero].
   assert (Nonzero:@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0).
   { apply Z.eqb_neq;rewrite canonical_scalar_zero_after_normalize;exact Zero. }
   assert (Flag0:Mem.load Mint32 m ba 120=Some (Vint Int.zero)).
   { unfold bit_int in Flag;rewrite Infinity in Flag;exact Flag. }
   assert (Finite:field_zero_result z=Int.zero).
   { rewrite (mixed_flag_of_residue z az HZ).
     rewrite <-literal_gej_is_infinity_value with (x:=ax) (y:=ay).
     exact (f_equal bit_int Infinity). }
   destruct (eval_strauss_general_finite Model raw ng ax ay az x y z m br bk ba bs bp bt bx bng
    Tables Ready Beta Separate Owned Input InputNG Nonzero BX BY BZ X Y Z Flag0 HX HY HZ Finite PS PT PX)
    as (mf & ox & oy & oz & Call & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedF & TablesF & Frame).
   exists mf,ox,oy,oz;split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];
    split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
   + rewrite literal_off_curve_linear_combination_1_value.
     change (((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
       if Bit.toBool (@literal_strauss_guard Alg.CoreFunSem ((raw,((ax,ay),az)),ng))
       then @literal_generate Alg.CoreFunSem ng
       else @literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),az)),ng)).
     rewrite Guard;exact Literal.
   + split;[exact OwnedF|];split;assumption.
Qed.
