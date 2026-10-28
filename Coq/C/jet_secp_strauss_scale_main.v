(** Original Strauss main stages and the whole skipped-preprocessing call. *)
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


Lemma strauss_nodup_disjoint {A:Type} (left right:list A) :
 NoDup (left++right) -> forall x,In x left -> ~In x right.
Proof.
 induction left as [|a left IH];cbn;intros ND x Member;[contradiction|].
 apply NoDup_cons_iff in ND;destruct ND as [Apart ND].
 destruct Member as [Same|Member].
 - subst x;intro Present;apply Apart;apply in_or_app;right;exact Present.
 - exact (IH ND x Member).
Qed.

Section Generic_strauss_zero_global_preserved.
Context (bng:block).
Lemma strauss_zero_global_preserved_at m mf :
 (zero_scalar_state bng) m -> readonly_preserved m mf -> (zero_scalar_state bng) mf.
Proof.
 intros Global Read;eapply (strauss_zero_global_unchanged_at bng);[exact Global|].
 eapply Mem.unchanged_on_implies;[exact (proj2 Read)|].
 intros b pos At Valid;subst b;split;[exact Valid|].
 apply (readonly_bounds_not_writable _ _ _ _ (proj2 Global)).
Qed.
End Generic_strauss_zero_global_preserved.

Lemma strauss_zero_global_preserved m mf :
 strauss_zero_global_state m -> readonly_preserved m mf -> strauss_zero_global_state mf.
Proof. exact (@strauss_zero_global_preserved_at strauss_zero_block m mf). Qed.

Section Generic_exec_strauss_scale_main.
Context (bng:block).
Theorem exec_strauss_scale_main_at (Model:memset_model) le m br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
 (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) xs ys aux inv last1 lastlam digits1 digitslam :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sign1:=wnaf5_input_sign (fst (fst halves)) in
 let signlam:=wnaf5_input_sign (fst (snd halves)) in
 NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 le!_bits=Some (Vint (Int.repr (Z.max (last1+1) (lastlam+1)))) ->
 le!_ng=Some (Vptr bng Ptrofs.zero) -> (zero_scalar_state bng) m ->
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
  @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ (zero_scalar_state bng) mf /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf.
Proof.
 cbn zeta;intros Separate R State No Bits NG Global PS PT PX C1 CL A1 AL L1 LL Table Bounds Tight Aux AuxBounds AuxLiteral
  InvBounds Inv Context FreeR FreeT FreeX Owned.
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw).
 pose (sign1:=wnaf5_input_sign (fst (fst halves))).
 pose (signlam:=wnaf5_input_sign (fst (snd halves))).
 fold halves in A1,AL,L1,LL;fold sign1 in A1,L1;fold signlam in AL,LL.
 destruct (strauss_wnaf5_array_for_loop m bp 0 (fst halves) digits1 sign1 last1 A1 L1) as [B1 D1].
 destruct (strauss_wnaf5_array_for_loop m bp 516 (snd halves) digitslam signlam lastlam AL LL) as [BL DL].
 assert (Small:NoDup [b0;b128;bw0;bw128]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;cbn [In] in Separate|-*;intuition congruence. }
 assert (StageSeparate:NoDup [br;bd;bs;bp;bt;bx;bz]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;cbn [In] in Separate|-*;intuition congruence. }
 assert (Protected:forall b,In b [br;bs;bp;bt;bx;bz] ->
  b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128).
 { pose proof (strauss_nodup_disjoint [br;bs;bp;bt;bx;bd;bz]
    [b0;b128;bw0;bw128;bj;bn;bl] Separate) as Apart.
   intros b Slot;assert (Member:In b [br;bs;bp;bt;bx;bd;bz]).
   { clear -Slot;cbn [In] in *;tauto. }
   specialize (Apart b Member);cbn [In] in Apart.
   repeat split;intuition congruence. }
 destruct ((exec_strauss_zero_generator_branch_at bng) Model e le m b0 b128 bw0 bw128
  (Z.max (last1+1) (lastlam+1)) Small eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  NG ltac:(lia) Bits Global
  (Owned b0 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned b128 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw0 516 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw128 516 ltac:(clear;cbn [generator_local_storage In];tauto)))
  as (mz & Branch & BitsZ & G1Z & G128Z & Low & High & F0 & F128 & FW0 & FW128 & GlobalZ & FrameZ & PermZ).
 pose (lz:=strauss_zero_wnaf_temps le).
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
 assert (RZ:lz!_r=Some (Vptr br Ptrofs.zero)).
 { unfold lz;rewrite strauss_zero_wnaf_other by (clear;cbn [In];intuition discriminate);exact R. }
 assert (SZ:lz!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold lz;rewrite strauss_zero_wnaf_other by (clear;cbn [In];intuition discriminate);exact State. }
 assert (NZ:lz!_no=Some (Vlong Int64.one)).
 { unfold lz;rewrite strauss_zero_wnaf_other by (clear;cbn [In];intuition discriminate);exact No. }
 assert (CountZ:lz!_bits=Some (Vint (Int.repr (Z.of_nat (Z.to_nat (Z.max (last1+1) (lastlam+1))))))).
 { rewrite Z2Nat.id by lia;exact BitsZ. }
 destruct (exec_strauss_scale_point_stage (Z.to_nat (Z.max (last1+1) (lastlam+1)))
  e lz mz br bs bp bd bt bx bz xs ys aux inv (last1+1) (lastlam+1)
  (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves))
  ltac:(lia) (strauss_local_env_plain bd bz b0 b128 bw0 bw128 bj bn bl) StageSeparate
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
   FreeRF & FreeDF & FreeTF & FreeXF & FreeZF & KeepStage & ReadStage & FrameStage).
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepZ|exact KeepStage]).
 assert (GlobalF:(zero_scalar_state bng) mf).
 { eapply (strauss_zero_global_preserved_at bng);[exact GlobalZ|exact ReadStage]. }
 assert (Literal:((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt)).
 { pose proof (f_equal (fun context:Ty.tySem literal_strauss_context=>
    let result:=strauss_scale_loop_result (Z.to_nat (Z.max (last1+1) (lastlam+1)))
     (strauss_wnaf5_digit_at (fst halves)) (strauss_wnaf5_digit_at (snd halves)) context
     (@literal_gej_infinity Alg.CoreFunSem tt) in
    (fst result,@literal_fe_multiply Alg.CoreFunSem (fst context,snd result))) Context) as ContextValue.
   exact (eq_trans LiteralStage (eq_trans ContextValue
    (strauss_scale_body_from_arrays m bp raw point sign1 signlam last1 lastlam digits1 digitslam A1 AL L1 LL))). }
 assert (Frame:lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameZ|intros b pos [Rr Other] _;clear -Other;cbn [In] in Other;intuition congruence].
   - eapply lframe_implies;[exact FrameStage|intros b pos [Rr Other] _;clear -Rr Other;cbn [In] in Other;intuition congruence]. }
 exists lef,mf,ox,oy,oz;split.
 - unfold generator_main_stage;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Branch|exact Stage].
 - split;[exact RF|];split;[exact X|];split;[exact Y|];split;[exact Z|];
   split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Literal|];
   split;[exact FreeRF|];split;[exact FreeTF|];split;[exact FreeXF|];split.
   + intros b hi Slot pos P;apply Keep;apply (Owned b hi Slot);exact P.
   + split;[exact Keep|];split;[exact GlobalF|exact Frame].
Qed.
End Generic_exec_strauss_scale_main.

Theorem exec_strauss_scale_main (Model:memset_model) le m br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl
 (raw:Ty.tySem (Word 8)) (point:Ty.tySem literal_table_gej) xs ys aux inv last1 lastlam digits1 digitslam :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sign1:=wnaf5_input_sign (fst (fst halves)) in
 let signlam:=wnaf5_input_sign (fst (snd halves)) in
 NoDup [br;bs;bp;bt;bx;bd;bz;b0;b128;bw0;bw128;bj;bn;bl] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 le!_bits=Some (Vint (Int.repr (Z.max (last1+1) (lastlam+1)))) ->
 le!_ng=Some (Vptr strauss_zero_block Ptrofs.zero) -> strauss_zero_global_state m ->
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
  @literal_strauss_body Alg.CoreFunSem ((raw,point),@Word.zero 8 Alg.CoreFunSem tt) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ strauss_zero_global_state mf /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf.
Proof. exact (@exec_strauss_scale_main_at strauss_zero_block Model le m br bs bp bt bx bd bz b0 b128 bw0 bw128 bj bn bl raw point xs ys aux inv last1 lastlam digits1 digitslam). Qed.

Require Import C.jet_secp_strauss_empty_stage.
Section Generic_exec_strauss_scale_main_empty.
Context (bng:block).
Theorem exec_strauss_scale_main_empty_at (Model:memset_model) le m br bd bz b0 b128 bw0 bw128 bj bn bl :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 NoDup [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_bits=Some (Vint Int.zero) ->
 le!_ng=Some (Vptr bng Ptrofs.zero) -> (zero_scalar_state bng) m ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 exists lef mf,
 Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
 fe_at mf br 0 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 40 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 80 (words5 (fun _=>Int64.zero)) /\
 Mem.load Mint32 mf br 120=Some (Vint Int.one) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ (zero_scalar_state bng) mf /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf.
Proof.
 cbn zeta;intros Separate R Bits NG Global FreeR Owned.
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 assert (Small:NoDup [b0;b128;bw0;bw128]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat rewrite NoDup_cons_iff;
   cbn [In] in Separate|-*;intuition congruence. }
 destruct ((exec_strauss_zero_generator_branch_at bng) Model e le m b0 b128 bw0 bw128 0
  Small eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl NG ltac:(clear;lia) Bits Global
  (Owned b0 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned b128 32 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw0 516 ltac:(clear;cbn [generator_local_storage In];tauto))
  (Owned bw128 516 ltac:(clear;cbn [generator_local_storage In];tauto)))
  as (mz & Branch & BitsZ & G1Z & G128Z & Low & High & F0 & F128 & FW0 & FW128 & GlobalZ & FrameZ & PermZ).
 pose (lz:=strauss_zero_wnaf_temps le).
 assert (RZ:lz!_r=Some (Vptr br Ptrofs.zero)).
 { unfold lz;rewrite strauss_zero_wnaf_other by (clear;cbn [In];intuition discriminate);exact R. }
 assert (KeepZ:keeps_permissions m mz).
 { intros b pos k p P;apply (proj2 (PermZ b pos k p (Mem.perm_valid_block _ _ _ _ _ P)));exact P. }
 destruct (exec_strauss_empty_point_stage e lz mz br eq_refl RZ BitsZ
  ltac:(intros pos P;apply KeepZ,FreeR;exact P))
  as (mf & Empty & X & Y & Z & Flag & FreeRF & FrameE & PermE).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p P;apply (proj2 (PermE b pos k p));apply KeepZ;exact P. }
 assert (GlobalF:(zero_scalar_state bng) mf).
 { eapply (strauss_zero_global_preserved_at bng);[exact GlobalZ|].
   eapply secp_closed_stmt_preserved;[exact Empty|apply strauss_local_env_plain|exact strauss_point_stage_closed]. }
 assert (Frame:lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameZ|intros b pos [Rr Other] _;clear -Other;cbn [In] in Other;intuition congruence].
   - eapply lframe_implies;[exact FrameE|intros b pos [Rr Other] _;exact Rr]. }
 exists (strauss_empty_stage_temps lz),mf;split.
 - unfold generator_main_stage;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Branch|exact Empty].
 - split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact Flag|];split;[exact FreeRF|];split.
   + intros b hi Slot pos P;apply Keep;apply (Owned b hi Slot);exact P.
   + split;[exact Keep|];split;assumption.
Qed.
End Generic_exec_strauss_scale_main_empty.

Theorem exec_strauss_scale_main_empty (Model:memset_model) le m br bd bz b0 b128 bw0 bw128 bj bn bl :
 let e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl in
 NoDup [bd;bz;b0;b128;bw0;bw128;bj;bn;bl] ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_bits=Some (Vint Int.zero) ->
 le!_ng=Some (Vptr strauss_zero_block Ptrofs.zero) -> strauss_zero_global_state m ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 exists lef mf,
 Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
 fe_at mf br 0 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 40 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 80 (words5 (fun _=>Int64.zero)) /\
 Mem.load Mint32 mf br 120=Some (Vint Int.one) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\
 (forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 keeps_permissions m mf /\ strauss_zero_global_state mf /\
 lframe (fun b _=>b<>br /\ ~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) m mf.
Proof. exact (@exec_strauss_scale_main_empty_at strauss_zero_block Model le m br bd bz b0 b128 bw0 bw128 bj bn bl). Qed.

Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_strauss_skip C.jet_secp_generator_function
 C.jet_secp_scalar_add_reader_support C.jet_secp_generator_initialize
 C.jet_secp_generator_globalz_call C.jet_secp_statement_prefix.

Section Generic_eval_strauss_scale_skipped.
Context (bng:block).
Theorem eval_strauss_scale_skipped_at (Model:memset_model) value m br bk ba bs bt bx :
 (zero_scalar_state bng) m -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 40 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 80 (words5 (fun _=>Int64.zero)) /\
 Mem.load Mint32 mf br 120=Some (Vint Int.one) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ (zero_scalar_state bng) mf /\
 lframe (fun b _=>b<>br) m mf.
Proof.
 intros Global Range Input Skip PT PX FreeR.
 assert (VR:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FreeR 0);clear;lia).
 pose proof ((strauss_zero_global_valid_at bng) m Global) as VG.
 destruct (strauss_entry_and_initialize m bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero))
  as (mi & mp & bd & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
   Entry & Init & Denominator & Separate & Old & Owned & FrameI & KeepI & ReadI).
 pose (e:=generator_local_env bd bz b0 b128 bw0 bw128 bj bn bl).
 pose (le:=strauss_entry_temps bs (Vptr br Ptrofs.zero) (Vptr ba Ptrofs.zero)
  (Vptr bk Ptrofs.zero) (Vptr bng Ptrofs.zero)).
 pose (li:=generator_initial_temps le).
 assert (Saved:forall chunk b ofs v,Mem.load chunk m b ofs=Some v -> Mem.load chunk mp b ofs=Some v).
 { intros chunk b ofs v Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact I].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (InputP:scalar_at mp bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value))).
 { eapply scalar_at_lframe;[exact Input|exact FrameI|intros;exact I]. }
 assert (SkipP:value=0 \/ Mem.load Mint32 mp ba 120=Some (Vint Int.one)).
 { destruct Skip as [Zero|Flag];[left;exact Zero|right;apply Saved;exact Flag]. }
 assert (PTP:Mem.load Mptr mp bs 8=Some (Vptr bt Ptrofs.zero)) by (apply Saved;exact PT).
 assert (PXP:Mem.load Mptr mp bs 0=Some (Vptr bx Ptrofs.zero)) by (apply Saved;exact PX).
 assert (NAI:li!_na=Some (Vptr bk Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (AI:li!_a=Some (Vptr ba Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (NumI:li!_num=Some (Vlong Int64.one)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (NoI:li!_no=Some (Vlong Int64.zero)) by (unfold li,generator_initial_temps;apply PTree.gss).
 assert (StateI:li!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 destruct (exec_strauss_no_points e li mp value bk ba bs bt bx eq_refl eq_refl eq_refl
  NAI AI NumI NoI StateI Range InputP SkipP PTP PXP)
  as (ms & SkipCall & NP & NoS & Other & UnchangedS & FrameS & KeepS & ReadS).
 pose (ls:=strauss_no_points_temps li value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 assert (RS:ls!_r=Some (Vptr br Ptrofs.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (BitsS:ls!_bits=Some (Vint Int.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li,generator_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 assert (NGS:ls!_ng=Some (Vptr bng Ptrofs.zero)).
 { unfold ls;rewrite Other by (clear;cbn [In];intuition discriminate).
   unfold li;rewrite generator_initial_preserves by discriminate;reflexivity. }
 assert (GlobalS:(zero_scalar_state bng) ms).
 { eapply (strauss_zero_global_preserved_at bng);[|exact ReadS].
   eapply (strauss_zero_global_preserved_at bng);[exact Global|exact ReadI]. }
 assert (FreeRS:Mem.range_perm ms br 0 128 Cur Freeable).
 { intros pos P;apply KeepS,KeepI,FreeR;exact P. }
 assert (OwnedS:forall b hi,In (b,hi) (generator_local_storage bd bz b0 b128 bw0 bw128 bj bn bl) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos P;apply KeepS;apply (Owned b hi Slot);exact P. }
 destruct ((exec_strauss_scale_main_empty_at bng) Model ls ms br bd bz b0 b128 bw0 bw128 bj bn bl
  Separate RS BitsS NGS GlobalS FreeRS OwnedS)
  as (lef & mu & Main & X & Y & Z & Flag & FreeRU & OwnedU & KeepM & GlobalU & FrameM).
 assert (OutsideR:~In br [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VR).
 assert (OutsideG:~In bng [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VG).
 destruct (free_list_exists
  [(bw128,0,516);(bw0,0,516);(bd,0,88);(bj,0,128);(bz,0,40);(b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)] mu)
  as (mf & Released & UnchangedF).
 - pose proof Separate as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
   clear -Distinct;cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;clear -OwnedU Slot;cbn [In] in Slot.
   repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
    inversion Slot;subst;apply OwnedU;clear;cbn [generator_local_storage In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bd;bz;b0;b128;bw0;bw128;bj;bn;bl]) mu mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
   assert (XF:fe_at mf br 0 (words5 (fun _=>Int64.zero))).
   { eapply field_at_lframe;[exact X|exact FrameF|intros;exact OutsideR]. }
   assert (YF:fe_at mf br 40 (words5 (fun _=>Int64.zero))).
   { eapply field_at_lframe;[exact Y|exact FrameF|intros;exact OutsideR]. }
   assert (ZF:fe_at mf br 80 (words5 (fun _=>Int64.zero))).
   { eapply field_at_lframe;[exact Z|exact FrameF|intros;exact OutsideR]. }
   assert (FlagF:Mem.load Mint32 mf br 120=Some (Vint Int.one)).
   { rewrite (proj1 FrameF Mint32 br 120);[exact Flag| |intros;exact OutsideR].
     eapply Mem.perm_valid_block;apply (FreeRU 0);clear;lia. }
   assert (FreeRF:Mem.range_perm mf br 0 128 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FreeRU|exact FrameF|intros;exact OutsideR]. }
   assert (GlobalF:(zero_scalar_state bng) mf).
   { eapply (strauss_zero_global_unchanged_at bng);[exact GlobalU|].
     eapply Mem.unchanged_on_implies;[exact UnchangedF|].
     intros b pos At Valid;subst b;clear -OutsideG;cbn [map fst In] in *;intuition congruence. }
   assert (Frame:lframe (fun b _=>b<>br) m mf).
   { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>br).
     - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
       eapply lframe_trans;[eapply lframe_implies;[exact FrameS|intros;exact I]|].
       eapply lframe_trans.
       + eapply lframe_implies;[exact FrameM|intros b pos [Valid NotR] _;split;[exact NotR|apply Old;exact Valid]].
       + eapply lframe_implies;[exact FrameF|intros b pos [Valid NotR] _;apply Old;exact Valid].
     - intros b pos NotR Valid;split;assumption. }
   assert (Prepare:Clight2.exec_stmt secp_ge e le mi generator_prepare_non_generator E0 ls ms Out_normal).
   { rewrite generator_prepare_non_generator_source;eapply exec_statement_prefix_then_last;[exact Init|exact SkipCall]. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mu) (out:=Out_normal).
     * exact Entry.
     * rewrite generator_body_main_source;eapply exec_statement_prefix_then_last;[exact Prepare|exact Main].
     * reflexivity.
     * unfold e;rewrite generator_local_blocks;exact Released.
   + split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact FlagF|];
     split;[exact FreeRF|];split;assumption.
Qed.
End Generic_eval_strauss_scale_skipped.

Theorem eval_strauss_scale_skipped (Model:memset_model) value m br bk ba bs bt bx :
 strauss_zero_global_state m -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (C.jet_secp_scalar_get_b32_numeric.scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.range_perm m br 0 128 Cur Freeable ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
  [Vptr bs Ptrofs.zero;Vptr br Ptrofs.zero;Vlong Int64.one;Vptr ba Ptrofs.zero;
   Vptr bk Ptrofs.zero;Vptr strauss_zero_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 40 (words5 (fun _=>Int64.zero)) /\
 fe_at mf br 80 (words5 (fun _=>Int64.zero)) /\
 Mem.load Mint32 mf br 120=Some (Vint Int.one) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ strauss_zero_global_state mf /\
 lframe (fun b _=>b<>br) m mf.
Proof. exact (@eval_strauss_scale_skipped_at strauss_zero_block Model value m br bk ba bs bt bx). Qed.
