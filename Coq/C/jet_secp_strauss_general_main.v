(** Original Strauss main phase with a prepared point table and arbitrary generator scalar. *)
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


From Coq Require Import Sorting.Permutation.
Require Import C.jet_secp_strauss_general_iteration C.jet_secp_strauss_general_loop C.jet_secp_strauss_general_point_stage
 C.jet_secp_strauss_general_arrays C.jet_secp_strauss_generator_branch C.jet_secp_generator_wnaf_general
 C.jet_secp_generator_pair_general C.jet_secp_generator_globals
 C.jet_secp_strauss_scale_main C.jet_secp_scalar_add_reader_support
 C.jet_secp_scalar_split128_literal C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_toZ.

Theorem exec_strauss_general_main_flag (Model:memset_model) le m bng br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
 (raw ng:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) xs ys aux inv last1 lastlam digits1 digitslam :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sign1:=wnaf5_input_sign (fst (fst halves)) in
 let signlam:=wnaf5_input_sign (fst (snd halves)) in
 NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl;bng] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 le!_bits=Some (Vint (Int.repr (Z.max (last1+1) (lastlam+1)))) ->
 le!_ng=Some (Vptr bng Ptrofs.zero) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 Mem.range_perm m bng 0 32 Cur Freeable -> (forall h,generator_table_state h m) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr (last1+1))) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr (lastlam+1))) ->
 wnaf_array_state m bp 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m bp 516 129 5 signlam 129 lastlam digitslam ->
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds inv -> fe_at m bz 0 (words5 inv) ->
 (rescale_field_output inv,globalz_word_vector (globalz_decoded_points xs ys))=
  @literal_scalar_table5 Alg.CoreFunSem point ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable ->
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
 lef!_r=Some (Vptr br Ptrofs.zero) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,point),ng) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf /\
 (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output inv))=false ->
  Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
Proof.
 cbn zeta;intros Separate R State No Bits NG InputNG FreeNG Tables PS PT PX C1 CL A1 AL L1 LL Table Bounds Tight Aux AuxBounds AuxLiteral
  InvBounds Inv Context FreeR FreeT FreeX Owned.
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw).
 pose (sign1:=wnaf5_input_sign (fst (fst halves))).
 pose (signlam:=wnaf5_input_sign (fst (snd halves))).
 fold halves in A1,AL,L1,LL;fold sign1 in A1,L1;fold signlam in AL,LL.
 destruct (strauss_wnaf5_array_for_loop m bp 0 (fst halves) digits1 sign1 last1 A1 L1) as [B1 D1].
 destruct (strauss_wnaf5_array_for_loop m bp 516 (snd halves) digitslam signlam lastlam AL LL) as [BL DL].
 assert (Small:NoDup [b0;b128;bw0;bw128;bng]).
 { pose proof (NoDup_app_remove_l [br;bs;bp;bt;bx;bd;bz]
   [b0;b128;bw0;bw128;bj;bn;bl;bng] Separate) as Tail.
   exact (strauss_nodup_splice [b0;b128;bw0;bw128] [bj;bn;bl] [bng] Tail). }
 assert (StageSeparate:NoDup [br;bd;bs;bp;bt;bx;bz;bw0;bw128]).
 { pose proof (strauss_nodup_splice [br;bs;bp;bt;bx;bd;bz] [b0;b128]
   [bw0;bw128;bj;bn;bl;bng] Separate) as Less.
   pose proof (NoDup_app_remove_r [br;bs;bp;bt;bx;bd;bz;bw0;bw128] [bj;bn;bl;bng] Less) as Raw.
   eapply Permutation_NoDup;[|exact Raw].
   apply Coq.Sorting.Permutation.perm_skip.
   apply Coq.Sorting.Permutation.Permutation_sym.
   exact (@Coq.Sorting.Permutation.Permutation_middle block [bs;bp;bt;bx] [bz;bw0;bw128] bd). }
 assert (Protected:forall b,In b [br;bs;bp;bt;bx;bz] ->
  b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128 /\ b<>bng).
 { pose proof (strauss_nodup_disjoint [br;bs;bp;bt;bx;bd;bz]
   [b0;b128;bw0;bw128;bj;bn;bl;bng] Separate) as Apart.
   intros b Slot;assert (Member:In b [br;bs;bp;bt;bx;bd;bz]) by
    (clear -Slot;cbn [In] in *;tauto).
   specialize (Apart b Member);cbn [In] in Apart;repeat split;intuition congruence. }
 destruct (exec_strauss_generator_branch Model e le m ng bng b0 b128 bw0 bw128
  (Z.max (last1+1) (lastlam+1)) Small
  (strauss_local_env_plain bd bz b0 b128 bw0 bw128 bj bn bl)
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl NG ltac:(lia) Bits InputNG FreeNG
  (Owned b0 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned b128 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw0 516 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw128 516 ltac:(clear;cbn [generator_local_storage In];tauto)))
  as (mz & lastg1 & lastg128 & digitsg1 & digitsg128 & Branch & BitsZ & G1Z & G128Z & TempsZ &
   AG1 & AG128 & LG1 & LG128 & PermZ & TablesTransport & FrameZ).
 pose (lz:=generator_wnaf_setup_temps_from le (Z.max (last1+1) (lastlam+1)) (lastg1+1) (lastg128+1)).
 assert (TablesZ:forall h,generator_table_state h mz) by (intro h;apply TablesTransport,Tables).
 destruct (wnaf_literal_array_for_generator mz bw0 0 (literal_split128_low ng) digitsg1 lastg1 AG1 LG1)
  as [BG1 DG1].
 destruct (wnaf_literal_array_for_generator mz bw128 0 (literal_split128_high ng) digitsg128 lastg128 AG128 LG128)
  as [BG128 DG128].
 assert (KeepZ:keeps_permissions m mz).
 { intros b pos k p P;apply (proj2 (PermZ b pos k p (Mem.perm_valid_block _ _ _ _ _ P)));exact P. }
 assert (Saved:forall chunk b ofs value,In b [br;bs;bp;bt;bx;bz] ->
  Mem.load chunk m b ofs=Some value -> Mem.load chunk mz b ofs=Some value).
 { intros chunk b ofs value Slot Load;rewrite (proj1 FrameZ chunk b ofs);[exact Load| |intros;apply Protected;exact Slot].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (PSZ:Mem.load Mptr mz bs 16=Some (Vptr bp Ptrofs.zero)).
 { eapply Saved;[clear;cbn [In];tauto|exact PS]. }
 assert (PTZ:Mem.load Mptr mz bs 8=Some (Vptr bt Ptrofs.zero)).
 { eapply Saved;[clear;cbn [In];tauto|exact PT]. }
 assert (PXZ:Mem.load Mptr mz bs 0=Some (Vptr bx Ptrofs.zero)).
 { eapply Saved;[clear;cbn [In];tauto|exact PX]. }
 assert (C1Z:Mem.load Mint32 mz bp 1032=Some (Vint (Int.repr (last1+1)))).
 { eapply Saved;[clear;cbn [In];tauto|exact C1]. }
 assert (CLZ:Mem.load Mint32 mz bp 1036=Some (Vint (Int.repr (lastlam+1)))).
 { eapply Saved;[clear;cbn [In];tauto|exact CL]. }
 assert (TableZ:globalz_table_rep mz bt xs ys).
 { intros k K;destruct (Table k K) as (TX & TY & TF);split.
   - eapply field_at_lframe;[exact TX|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto].
   - split.
     + eapply field_at_lframe;[exact TY|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto].
     + eapply Saved;[clear;cbn [In];tauto|exact TF]. }
 assert (AuxZ:forall k,(k<8)%nat -> fe_at mz bx (40*Z.of_nat k) (words5 (aux k))).
 { intros k K;eapply field_at_lframe;[apply Aux;exact K|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (InvZ:fe_at mz bz 0 (words5 inv)).
 { eapply field_at_lframe;[exact Inv|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (A1Z:wnaf_array_state mz bp 0 129 5 sign1 129 last1 digits1).
 { eapply wnaf_129_array_lframe;[exact A1|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (ALZ:wnaf_array_state mz bp 516 129 5 signlam 129 lastlam digitslam).
 { eapply wnaf_129_array_lframe;[exact AL|exact FrameZ|intros;apply Protected;clear;cbn [In];tauto]. }
 destruct (strauss_wnaf5_array_for_loop mz bp 0 (fst halves) digits1 sign1 last1 A1Z L1) as [_ DZ1].
 destruct (strauss_wnaf5_array_for_loop mz bp 516 (snd halves) digitslam signlam lastlam ALZ LL) as [_ DZL].
 assert (RZ:lz!_r=Some (Vptr br Ptrofs.zero)) by (unfold lz;rewrite TempsZ by discriminate;exact R).
 assert (SZ:lz!_state=Some (Vptr bs Ptrofs.zero)) by (unfold lz;rewrite TempsZ by discriminate;exact State).
 assert (NZ:lz!_no=Some (Vlong Int64.one)) by (unfold lz;rewrite TempsZ by discriminate;exact No).
 pose (count:=Z.to_nat (Z.max (Z.max (Z.max (last1+1) (lastlam+1)) (lastg1+1)) (lastg128+1))).
 assert (Count:(count<=129)%nat) by (unfold count;lia).
 assert (CountZ:lz!_bits=Some (Vint (Int.repr (Z.of_nat count)))).
 { unfold count;rewrite Z2Nat.id by lia;exact BitsZ. }

 destruct (exec_strauss_general_point_stage_flag count e lz mz br bs bp bd bt bx bz xs ys aux inv
  (last1+1) (lastlam+1) (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves))
  bw0 bw128 (lastg1+1) (lastg128+1)
  (wnaf_literal_digit_at (literal_split128_low ng)) (wnaf_literal_digit_at (literal_split128_high ng))
  Count (strauss_local_env_plain bd bz b0 b128 bw0 bw128 bj bn bl) StageSeparate TablesZ
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl BG1 BG128
  ltac:(intros j J;exact (proj1 (DG1 j J)))
  ltac:(intros j J;exact (proj1 (DG128 j J)))
  ltac:(intros j J;exact (proj1 (proj2 (DG1 j ltac:(lia)))))
  ltac:(intros j J;exact (proj1 (proj2 (DG128 j ltac:(lia)))))
  ltac:(intros j J Above;exact (proj2 (proj2 (DG1 j J)) Above))
  ltac:(intros j J Above;exact (proj2 (proj2 (DG128 j J)) Above))
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl RZ SZ NZ CountZ G1Z G128Z
  PSZ PTZ PXZ B1 BL C1Z CLZ
  ltac:(intros j J;exact (proj1 (DZ1 j ltac:(lia))))
  ltac:(intros j J;exact (proj1 (DZL j ltac:(lia))))
  ltac:(intros j J Above;exact (proj2 (DZ1 j J) Above))
  ltac:(intros j J Above;exact (proj2 (DZL j J) Above))
  TableZ Bounds Tight AuxZ AuxBounds AuxLiteral InvBounds InvZ
  ltac:(intros pos P;apply KeepZ,FreeR;exact P)
  ltac:(intros pos P;apply KeepZ;apply (Owned bd 88 ltac:(clear;cbn [generator_local_storage In];tauto));exact P)
  ltac:(intros pos P;apply KeepZ,FreeT;exact P)
  ltac:(intros pos P;apply KeepZ,FreeX;exact P)
  ltac:(intros pos P;apply KeepZ;apply (Owned bz 40 ltac:(clear;cbn [generator_local_storage In];tauto));exact P))
  as (lef & mf & ox & oy & oz & Stage & RF & X & Y & Z & BX & BY & BZ & LiteralStage &
   FreeRF & FreeDF & FreeTF & FreeXF & FreeZF & KeepStage & ReadStage & FrameStage & ConditionalFlag).
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepZ|exact KeepStage]).
 assert (TablesF:forall h,generator_table_state h mf) by
  (eapply generator_tables_readonly;[exact TablesZ|exact ReadStage]).
 assert (Literal:((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,point),ng)).
 { pose proof (f_equal (fun context:Ty.tySem literal_strauss_context=>
    let result:=strauss_general_loop_result count
     (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves))
     (wnaf_literal_digit_at (literal_split128_low ng)) (wnaf_literal_digit_at (literal_split128_high ng)) context
     (@literal_gej_infinity Alg.CoreFunSem tt) in
    (fst result,@literal_fe_multiply Alg.CoreFunSem (fst context,snd result))) Context) as ContextValue.
   exact (eq_trans LiteralStage (eq_trans ContextValue
    (strauss_body_from_four_arrays mz bp bw0 bw128 raw ng point sign1 signlam last1 lastlam
     lastg1 lastg128 digits1 digitslam digitsg1 digitsg128 A1Z ALZ AG1 AG128 L1 LL LG1 LG128))). }
 assert (Frame:lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameZ|].
     intros b pos [Rr [Other NG0]] _;clear -Other NG0;cbn [In] in Other;intuition congruence.
   - eapply lframe_implies;[exact FrameStage|].
     intros b pos [Rr [Other NG0]] _;clear -Rr Other;cbn [In] in Other;intuition congruence. }
 exists lef,mf,ox,oy,oz;split.
 - unfold generator_main_stage;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Branch|exact Stage].
 - split;[exact RF|];split;[exact X|];split;[exact Y|];split;[exact Z|];
   split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Literal|];
   split;[exact FreeRF|];split;[exact FreeTF|];split;[exact FreeXF|];split.
   + intros b hi Slot pos Range;apply Keep;apply (Owned b hi Slot);exact Range.
   + split;[exact Keep|];split;[exact TablesF|];split;[exact Frame|exact ConditionalFlag].
Qed.


Theorem exec_strauss_general_main (Model:memset_model) le m bng br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
 (raw ng:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) xs ys aux inv last1 lastlam digits1 digitslam :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sign1:=wnaf5_input_sign (fst (fst halves)) in
 let signlam:=wnaf5_input_sign (fst (snd halves)) in
 NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl;bng] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 le!_bits=Some (Vint (Int.repr (Z.max (last1+1) (lastlam+1)))) ->
 le!_ng=Some (Vptr bng Ptrofs.zero) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 Mem.range_perm m bng 0 32 Cur Freeable -> (forall h,generator_table_state h m) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr (last1+1))) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr (lastlam+1))) ->
 wnaf_array_state m bp 0 129 5 sign1 129 last1 digits1 ->
 wnaf_array_state m bp 516 129 5 signlam 129 lastlam digitslam ->
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun j=>sign1*digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun j=>signlam*digitslam (Z.of_nat j)) (seq 0 129)) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds inv -> fe_at m bz 0 (words5 inv) ->
 (rescale_field_output inv,globalz_word_vector (globalz_decoded_points xs ys))=
  @literal_scalar_table5 Alg.CoreFunSem point ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable ->
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
 lef!_r=Some (Vptr br Ptrofs.zero) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,point),ng) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf.
Proof.
 cbn zeta;intros Separate R State No Bits NG InputNG FreeNG Tables PS PT PX C1 CL A1 AL L1 LL Table Bounds Tight Aux AuxBounds AuxLiteral
  InvBounds Inv Context FreeR FreeT FreeX Owned.
 destruct (exec_strauss_general_main_flag Model le m bng br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl raw ng point xs ys aux inv last1 lastlam digits1 digitslam
  Separate R State No Bits NG InputNG FreeNG Tables PS PT PX C1 CL A1 AL L1 LL Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv Context FreeR FreeT FreeX Owned)
  as (lef & mf & ox & oy & oz & Exec & ROut & X & Y & Z & BX & BY & BZ & Literal &
   FR & FT & FX & OwnedOut & Keep & TablesOut & Frame & Conditional).
 exists lef,mf,ox,oy,oz;repeat first [assumption|split].
Qed.
