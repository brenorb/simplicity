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

Require Import C.jet_secp_strauss_point_prefix C.jet_secp_generator_pair_general C.jet_secp_strauss_digit_add
 C.jet_secp_generator_globals C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_array.
Local Opaque C.jet_secp_add_literal.literal_gej_ge_add C.jet_secp_lookup5_literal.literal_lookup5
 C.jet_secp_table_get_lambda_literal.literal_ge_scale_lambda
 C.jet_secp_generate_literal.literal_generate_small literal_gej_zinv.


Require Import C.jet_secp_strauss_general_iteration C.jet_transport C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_generator_globals.
Require Import C.jet_elements_taptweak_strauss_transport C.jet_elements_taptweak_generator_pair.
Local Opaque elements_taptweak_ge.
Theorem exec_elements_taptweak_strauss_iteration (d1 dlam:Ty.tySem literal_wnaf5_digit) (dg1 dg128:Ty.tySem literal_wnaf_digit)
 xs ys aux x y z inv (ax ay az zctx:Ty.tySem (Word 8)) e le m br bs bp bd bt bx bb bg1 bg128 i bits1 bitslam bitsg1 bitsg128 :
 0<=i<129 -> 0<=bits1<=129 -> 0<=bitslam<=129 -> 0<=bitsg1<=129 -> 0<=bitsg128<=129 ->
 wnaf_literal_valid dg1 -> wnaf_literal_valid dg128 -> NoDup [br;bd;bs;bp;bt;bx;bb;bg1;bg128] ->
 plain_env e ->
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 (forall h,elements_taptweak_generator_table_state h m) ->
 e!_wnaf_ng_1=Some (bg1,tarray tint 129) -> e!_wnaf_ng_128=Some (bg128,tarray tint 129) ->
 e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_ecmult_table_get_ge_storage=None ->
 e!_secp256k1_gej_add_zinv_var=None -> e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!_secp256k1_ecmult_table_get_ge=None -> e!_secp256k1_ecmult_table_get_ge_lambda=None ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_gej_double_var=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr i)) -> le!_no=Some (Vlong Int64.one) ->
 le!_bits_ng_1=Some (Vint (Int.repr bitsg1)) -> le!_bits_ng_128=Some (Vint (Int.repr bitsg128)) ->
 (i<bitsg1 -> Mem.load Mint32 m bg1 (4*i)=Some (Vint (Int.repr (wnaf_literal_value dg1)))) ->
 (i<bitsg128 -> Mem.load Mint32 m bg128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value dg128)))) ->
 (bitsg1<=i -> dg1=inl tt) -> (bitsg128<=i -> dg128=inl tt) ->
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
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) zctx mod feP -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bb 0 40 Cur Freeable ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_loop_arithmetic E0
  (strauss_general_iteration_temps le bp bt bx i bits1 bitslam bitsg1 bitsg128 d1 dlam dg1 dg128) mf Out_normal /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_step Alg.CoreFunSem
   (((ax,ay),az),((zctx,globalz_word_vector (globalz_decoded_points xs ys)),((d1,dlam),(dg1,dg128)))) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 fe_at mf bb 0 (words5 inv) /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 (forall h,elements_taptweak_generator_table_state h mf) /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd /\ b<>bb) m mf.

Proof.
 intros Index Len1 LenLam LenG1 LenG128 ValidG1 ValidG128 Separate Plain Domain BoundLocals Tables
  ArrayG1 ArrayG128 LocalZ GetStorage AddZinv TableG1 TableG128
  Local Get GetLam Add DoubleSymbol R State I No G1 G128 LoadG1 LoadG128 AbsentG1 AbsentG128
  PS PT PX Count1 CountLam Load1 LoadLam Absent1 AbsentLam Table Bounds Tight Aux AuxBounds AuxLiteral
  BX BY BZ BI Scale Inv FreeZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 assert (PrefixSep:NoDup [br;bd;bs;bp;bt;bx]).
 { exact (NoDup_app_remove_r [br;bd;bs;bp;bt;bx] [bb;bg1;bg128] Separate). }
 assert (PairSep:NoDup [br;bd;bb;bg1;bg128]).
 { exact (strauss_nodup_splice [br;bd] [bs;bp;bt;bx] [bb;bg1;bg128] Separate). }
 assert (Protected:forall b,In b [bb;bg1;bg128] -> b<>br /\ b<>bd).
 { pose proof PairSep as Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep.
   intros b Member;cbn [In] in Member;intuition congruence. }
 destruct (exec_strauss_point_prefix d1 dlam xs ys aux x y z ax ay az
  e le m br bs bp bd bt bx i bits1 bitslam Index Len1 LenLam PrefixSep
  Local Get GetLam Add DoubleSymbol R State I No PS PT PX Count1 CountLam
  Load1 LoadLam Absent1 AbsentLam Table Bounds Tight Aux AuxBounds AuxLiteral
  BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX)
  as (md & mp & px & py & pz & Double & Point & XP & YP & ZP & FlagP &
   BXP & BYP & BZP & LiteralP & FRP & FDP & FTP & FXP & KeepP & ReadonlyP & FrameP).
 pose (lp:=strauss_point_loop_temps le bp bt bx i bits1 bitslam d1 dlam).
 assert(DoubleT:Clight2.exec_stmt elements_taptweak_ge e le m generator_double_statement E0 le md Out_normal).
 { eapply elements_taptweak_strauss_bound_statement_transport;
   [exact Domain|exact BoundLocals|left;reflexivity|exact Double]. }
 assert(PointT:Clight2.exec_stmt elements_taptweak_ge e le md generator_nongenerator_statement E0 lp mp Out_normal).
 { eapply elements_taptweak_strauss_bound_statement_transport;
   [exact Domain|exact BoundLocals|right;left;reflexivity|exact Point]. }

 assert (RP:lp!_r=Some (Vptr br Ptrofs.zero)).
 { unfold lp;rewrite strauss_point_loop_other by (clear;cbn [In];intuition discriminate);exact R. }
 assert (IP:lp!_i=Some (Vint (Int.repr i))).
 { unfold lp;rewrite strauss_point_loop_other by (clear;cbn [In];intuition discriminate);exact I. }
 assert (G1P:lp!_bits_ng_1=Some (Vint (Int.repr bitsg1))).
 { unfold lp;rewrite strauss_point_loop_other by (clear;cbn [In];intuition discriminate);exact G1. }
 assert (G128P:lp!_bits_ng_128=Some (Vint (Int.repr bitsg128))).
 { unfold lp;rewrite strauss_point_loop_other by (clear;cbn [In];intuition discriminate);exact G128. }
 assert (Saved:forall chunk b ofs value,In b [bb;bg1;bg128] ->
  Mem.load chunk m b ofs=Some value -> Mem.load chunk mp b ofs=Some value).
 { intros chunk b ofs value Member Load;rewrite (proj1 FrameP chunk b ofs);[exact Load| |].
   - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact Load|constructor].
   - intros;apply Protected;exact Member. }
 assert (LoadG1P:i<bitsg1 -> Mem.load Mint32 mp bg1 (4*i)=Some (Vint (Int.repr (wnaf_literal_value dg1)))).
 { intro Range;apply Saved;[clear;cbn [In];tauto|apply LoadG1;exact Range]. }
 assert (LoadG128P:i<bitsg128 -> Mem.load Mint32 mp bg128 (4*i)=Some (Vint (Int.repr (wnaf_literal_value dg128)))).
 { intro Range;apply Saved;[clear;cbn [In];tauto|apply LoadG128;exact Range]. }
 assert (InvP:fe_at mp bb 0 (words5 inv)).
 { eapply field_at_lframe;[exact Inv|exact FrameP|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (FZP:Mem.range_perm mp bb 0 40 Cur Freeable) by (intros pos Range;apply KeepP,FreeZ;exact Range).
 assert (TablesP:forall h,elements_taptweak_generator_table_state h mp) by
  (eapply elements_taptweak_generator_tables_readonly;[exact Tables|exact ReadonlyP]).
 destruct (exec_elements_taptweak_generator_pair_scaled dg1 dg128 px py pz inv
  (rescale_field_output px) (rescale_field_output py) (rescale_field_output pz) zctx
  e lp mp i bitsg1 bitsg128 bg1 bg128 br bd bb
  Index LenG1 LenG128 ValidG1 ValidG128 PairSep TablesP RP IP G1P G128P
  ArrayG1 ArrayG128 Local LocalZ GetStorage AddZinv TableG1 TableG128
  LoadG1P LoadG128P AbsentG1 AbsentG128 BXP BYP BZP BI Scale eq_refl
  FlagP XP YP ZP InvP FRP FDP FZP)
  as (mf & ox & oy & oz & Gens & XO & YO & ZO & FlagO & InvO & FRF & FDF & FZF &
   BXO & BYO & BZO & LiteralG & TablesF & FrameG).
 destruct (elements_taptweak_generator_pair_effects _ _ _ _ _ _ _ Gens Plain) as [KeepG ReadonlyG].
 assert (Literal:((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_step Alg.CoreFunSem
   (((ax,ay),az),((zctx,globalz_word_vector (globalz_decoded_points xs ys)),((d1,dlam),(dg1,dg128))))).
 { rewrite LiteralP in LiteralG;rewrite <-strauss_general_digit_actions in LiteralG;exact LiteralG. }
 exists mf,ox,oy,oz;split.
 - rewrite generator_loop_arithmetic_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=md);[exact DoubleT|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lp) (m1:=mp);[exact PointT|exact Gens].
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact Literal|];
   split;[exact FRF|];split;[exact FDF|];split.
   + intros pos Range;apply KeepG,FTP;exact Range.
   + split.
     * intros pos Range;apply KeepG,FXP;exact Range.
     * split;[exact InvO|];split;[exact FZF|];split;[exact TablesF|];split.
       -- eapply keeps_permissions_trans;[exact KeepP|exact KeepG].
       -- split.
          ++ eapply preserved_trans;[exact ReadonlyP|exact ReadonlyG].
          ++ eapply lframe_trans;[|exact FrameG].
             eapply lframe_implies;[exact FrameP|intros b pos (NR & ND & NZ) _;split;assumption].
Qed.

