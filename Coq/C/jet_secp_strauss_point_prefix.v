(** Original double and two point-digit dispatches, independent of generator counts. *)
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

Theorem exec_strauss_point_prefix (d1 dlam:Ty.tySem literal_wnaf5_digit)
 xs ys aux x y z (ax ay az:Ty.tySem (Word 8)) e le m br bs bp bd bt bx i bits1 bitslam :
 0<=i<129 -> 0<=bits1<=129 -> 0<=bitslam<=129 -> NoDup [br;bd;bs;bp;bt;bx] ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!_secp256k1_ecmult_table_get_ge=None -> e!_secp256k1_ecmult_table_get_ge_lambda=None ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_gej_double_var=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr i)) -> le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (i<bits1 -> Mem.load Mint32 m bp (4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value d1)))) ->
 (i<bitslam -> Mem.load Mint32 m bp (516+4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value dlam)))) ->
 (bits1<=i -> d1=inl tt) -> (bitslam<=i -> dlam=inl tt) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists md mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_double_statement E0 le md Out_normal /\
 Clight2.exec_stmt secp_ge e le md generator_nongenerator_statement E0
  (strauss_point_loop_temps le bp bt bx i bits1 bitslam d1 dlam) mf Out_normal /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  strauss_digit_action true dlam xs ys (strauss_digit_action false d1 xs ys
   (@literal_gej_double Alg.CoreFunSem ((ax,ay),az))) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd) m mf.
Proof.
 intros Index Len1 LenLam Separate Local Get GetLam Add DoubleSymbol R State I No
  PS PT PX Count1 CountLam Load1 LoadLam Absent1 AbsentLam Table Bounds Tight Aux AuxBounds AuxLiteral
  BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 assert (Protected:forall b,In b [bd;bs;bp;bt;bx] -> b<>br).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;
   intros b Member;cbn [In] in Member;intuition congruence. }
 assert (RX:radix_value x mod feP=@toZ (WordToZ 8) ax mod feP).
 { assert (Eq:rescale_field_output x=ax) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 assert (RY:radix_value y mod feP=@toZ (WordToZ 8) ay mod feP).
 { assert (Eq:rescale_field_output y=ay) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 assert (RZ:radix_value z mod feP=@toZ (WordToZ 8) az mod feP).
 { assert (Eq:rescale_field_output z=az) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 destruct (eval_double_var_loose_literal x y z ax ay az m br BX BY BZ RX RY RZ Flag X Y Z FreeR)
  as (md & dx & dy & dz & Double & XD & YD & ZD & FlagD & FRD & BXD & BYD & BZD & LiteralD & FrameD).
 assert (KeepD:keeps_permissions m md) by
  (eapply secp_internal_keeps_permissions;[exact strauss_double_var_closed|reflexivity|exact Double]).
 assert (ReadonlyD:readonly_preserved m md) by
  (eapply secp_closed_function_preserved;[exact strauss_double_var_closed|reflexivity|exact Double]).
 assert (Saved:forall chunk b ofs value,b<>br ->
  Mem.load chunk m b ofs=Some value -> Mem.load chunk md b ofs=Some value).
 { intros chunk b ofs value Outside Load;rewrite (proj1 FrameD chunk b ofs);[exact Load| |intros;exact Outside].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (PSD:Mem.load Mptr md bs 16=Some (Vptr bp Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PS]. }
 assert (PTD:Mem.load Mptr md bs 8=Some (Vptr bt Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PT]. }
 assert (PXD:Mem.load Mptr md bs 0=Some (Vptr bx Ptrofs.zero)).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PX]. }
 assert (C1D:Mem.load Mint32 md bp 1032=Some (Vint (Int.repr bits1))).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact Count1]. }
 assert (CLD:Mem.load Mint32 md bp 1036=Some (Vint (Int.repr bitslam))).
 { apply Saved;[apply Protected;clear;cbn [In];tauto|exact CountLam]. }
 assert (L1D:i<bits1 -> Mem.load Mint32 md bp (4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value d1)))).
 { intro H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply Load1;exact H]. }
 assert (LLD:i<bitslam -> Mem.load Mint32 md bp (516+4*i)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value dlam)))).
 { intro H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadLam;exact H]. }
 assert (TableD:globalz_table_rep md bt xs ys).
 { intros k K;destruct (Table k K) as (TX & TY & TF);split.
   - eapply field_at_lframe;[exact TX|exact FrameD|intros;apply Protected;clear;cbn [In];tauto].
   - split.
     + eapply field_at_lframe;[exact TY|exact FrameD|intros;apply Protected;clear;cbn [In];tauto].
     + apply Saved;[apply Protected;clear;cbn [In];tauto|exact TF]. }
 assert (AuxD:forall k,(k<8)%nat -> fe_at md bx (40*Z.of_nat k) (words5 (aux k))).
 { intros k K;eapply field_at_lframe;[apply Aux;exact K|exact FrameD|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (FDD:Mem.range_perm md bd 0 88 Cur Freeable) by (intros p P;apply KeepD,FreeD;exact P).
 assert (FTD:Mem.range_perm md bt 0 704 Cur Freeable) by (intros p P;apply KeepD,FreeT;exact P).
 assert (FXD:Mem.range_perm md bx 0 320 Cur Freeable) by (intros p P;apply KeepD,FreeX;exact P).
 destruct (exec_strauss_single_point_loop d1 dlam xs ys aux dx dy dz
  (rescale_field_output dx) (rescale_field_output dy) (rescale_field_output dz)
  e le md br bs bp bd bt bx i bits1 bitslam Index Len1 LenLam Separate Local Get GetLam Add R State I No
  PSD PTD PXD C1D CLD L1D LLD Absent1 AbsentLam TableD Bounds Tight AuxD AuxBounds AuxLiteral
  BXD BYD BZD eq_refl XD YD ZD FlagD FRD FDD FTD FXD)
  as (mf & ox & oy & oz & Point & XO & YO & ZO & FlagO & BXO & BYO & BZO & LiteralP &
   FRF & FDF & FTF & FXF & KeepP & ReadonlyP & FrameP).
 exists md,mf,ox,oy,oz;split.
 - unfold generator_double_statement;eapply exec_curve_call with
      (vargs:=[Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact DoubleSymbol.
   + eapply eval_Econs with (v1:=Vptr br Ptrofs.zero);[apply eval_Etempvar;exact R|reflexivity|].
       eapply eval_Econs with (v1:=Vptr br Ptrofs.zero);[apply eval_Etempvar;exact R|reflexivity|].
       eapply eval_Econs with (v1:=Vlong Int64.zero);
        [eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
   + exact Double.
 - split;[exact Point|];rewrite LiteralD in LiteralP.
   split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact LiteralP|];
   split;[exact FRF|];split;[exact FDF|];split;[exact FTF|];split;[exact FXF|];split.
   + eapply keeps_permissions_trans;[exact KeepD|exact KeepP].
   + split.
     * eapply preserved_trans;[exact ReadonlyD|exact ReadonlyP].
     * eapply lframe_trans;[|exact FrameP];eapply lframe_implies;
        [exact FrameD|intros b p [B _] _;exact B].
Qed.
