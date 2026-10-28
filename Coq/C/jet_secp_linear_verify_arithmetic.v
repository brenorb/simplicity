(** Derive the four arithmetic helper calls of linear_verify_1. The table
    denominator condition is discharged from the original affine curve guard. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_readBit_layout C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_rescale_public_reads C.jet_secp_point_three_reads
 C.jet_secp_strauss_complete_program C.jet_secp_curve_literal C.jet_secp_linear_startup C.jet_secp_ecmult_general
 C.jet_secp_gej_set_ge_owned C.jet_secp_affine_negate_call C.jet_secp_field_weak_loose
 C.jet_secp_field_negate_separate C.jet_secp_field_mul_small C.jet_secp_mixed_finite_prefix
 C.jet_secp_mixed_xy_framed C.jet_secp_mixed_xy_literal C.jet_secp_mixed_infinite_literal
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_square_spec_bridge C.jet_secp_rescale_literal C.jet_secp_point_write_field C.jet_secp_point_field_bridge
 C.jet_secp_gej_negate_literal C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_secp_negate_literal_contract C.jet_secp_multiply_input_input C.jet_toZ C.jet_word_repr
 C.jet_secp_point_set_bit C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_literal_gej_predicate C.jet_secp_odd_table_literal_walk
 C.jet_secp_table_affine_nonzero C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_canonical_scalar C.jet_memset_model C.jet_secp_add_literal
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma linear_verify_negate_value (x y:Ty.tySem (Word 8)) :
 @literal_ge_negate Alg.CoreFunSem (x,y)=
 (@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y).
Proof. unfold literal_ge_negate;reflexivity. Qed.
Local Opaque secp_ge literal_ge_is_on_curve literal_off_curve_linear_combination_1
 literal_gej_ge_add literal_fe_one256 literal_ge_negate rescale_field_output canonical_fe_normalize.

Definition linear_verify_arithmetic_storage (ba bb bk bg br bz:block) :=
 [(ba,88);(bb,88);(bk,32);(bg,32);(br,128);(bz,128)].
Lemma linear_verify_one_residue : table_word_literal (point_set_bit_words true)
 (@literal_fe_one256 Alg.CoreFunSem tt).
Proof.
 unfold table_word_literal;rewrite literal_fe_one256_value.
 change (1 mod feP=1 mod feP);reflexivity.
Qed.
Lemma linear_verify_reader_residue value : table_word_literal (square_reader_rho value) value.
Proof.
 unfold table_word_literal;rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.
Lemma linear_verify_negated_bounds value :
 square_input_bounds (negate_sep_words (square_reader_rho value)).
Proof.
 assert (Small:mul_small_input_bounds (square_reader_rho value)).
 { apply mixed_positioned_tight;exact (proj1 (point_reader_limb_model _ (normalized_value_range value))). }
 exact (proj2 (negate_sep_numeric _ Small)).
Qed.
Lemma linear_verify_negated_output value :
 rescale_field_output (negate_sep_words (square_reader_rho value))=
 @literal_fe_negate Alg.CoreFunSem value.
Proof.
 change (point_field_output (point_negative_field
  (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))=
  @literal_fe_negate Alg.CoreFunSem value).
 apply point_normalized_negative_field_output.
Qed.
Lemma linear_verify_small_calls_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_gej_set_ge)=true /\
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_ge_neg)=true.
Proof. vm_compute;split;reflexivity. Qed.

Theorem eval_linear_verify_arithmetic (Model:memset_model)
 (raw ng ax ay bxword byword:Ty.tySem (Word 8)) m ba bb bk bg br bz :
 linear_startup m -> NoDup [ba;bb;bk;bg;br;bz] ->
 (forall b hi,In (b,hi) (linear_verify_arithmetic_storage ba bb bk bg br bz) ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 scalar_at m bg 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))) ->
 fe_at m ba 0 (point_canonical_limbs ax) -> fe_at m ba 40 (point_canonical_limbs ay) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bb 0 (point_canonical_limbs bxword) -> fe_at m bb 40 (point_canonical_limbs byword) ->
 Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=true ->
 exists ms mn mm mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_ge)
  [Vptr bz Ptrofs.zero;Vptr ba Ptrofs.zero] E0 ms Vundef /\
 Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_ge_neg)
  [Vptr bb Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mn Vundef /\
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_ecmult)
  [Vptr br Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mm Vundef /\
 Clight2.eval_funcall secp_ge mm (Internal f_secp256k1_gej_add_ge_var)
  [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem
    (@literal_gej_ge_add Alg.CoreFunSem
     (@literal_off_curve_linear_combination_1 Alg.CoreFunSem
       ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng),
      @literal_ge_negate Alg.CoreFunSem (bxword,byword))))))) /\
 (forall b hi,In (b,hi) (linear_verify_arithmetic_storage ba bb bk bg br bz) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 linear_startup mf /\ lframe (fun b _=>~In b [ba;bb;bk;bg;br;bz]) m mf.
Proof.
 intros Ready Separate Owned Input InputNG XA YA FlagA XB YB FlagB GuardA.
 assert (Apart:ba<>bb /\ ba<>bk /\ ba<>bg /\ ba<>br /\ ba<>bz /\
  bb<>bk /\ bb<>bg /\ bb<>br /\ bb<>bz /\ bk<>bg /\ bk<>br /\ bk<>bz /\ bg<>br /\ bg<>bz /\ br<>bz).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 destruct Apart as (AB & AK & AG & AR & AZ & BK & BG & BR & BZ & KG & KR & KZ & GR & GZ & RZ).
 assert (FZ:Mem.range_perm m bz 0 128 Cur Freeable)
  by (apply Owned;clear;cbn [linear_verify_arithmetic_storage In];tauto).
 rewrite !rescale_reader_limbs in XA,YA.
 destruct (eval_gej_set_ge_owned m bz ba (square_reader_rho ax) (square_reader_rho ay) Int.zero
   (not_eq_sym AZ) FZ XA YA FlagA)
  as (ms & SetCall & XZ & YZ & ZZ & FlagZ & FZS & FrameS).
 assert (OwnedS:forall b hi,In (b,hi) (linear_verify_arithmetic_storage ba bb bk bg br bz) ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (peq b bz) as [Same|Different].
   - subst b;cbn [linear_verify_arithmetic_storage In] in Slot;
     repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
     inversion Slot;subst;try congruence;exact FZS.
   - eapply curve_keep_free;[|apply Owned;exact Slot|exact FrameS|intros;exact Different].
     cbn [linear_verify_arithmetic_storage In] in Slot;
     repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
     inversion Slot;subst;lia. }
 assert (XBS:fe_at ms bb 0 (point_canonical_limbs bxword))
  by (eapply field_at_lframe;[exact XB|exact FrameS|intros;exact BZ]).
 assert (YBS:fe_at ms bb 40 (point_canonical_limbs byword))
  by (eapply field_at_lframe;[exact YB|exact FrameS|intros;exact BZ]).
 assert (ValidB:Mem.valid_block m bb).
 { eapply Mem.perm_valid_block;apply (Owned bb 88 ltac:(clear;cbn [linear_verify_arithmetic_storage In];tauto) 0);lia. }
 assert (FlagBS:Mem.load Mint32 ms bb 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameS Mint32 bb 80 ValidB ltac:(intros;exact BZ));exact FlagB. }
 destruct (eval_affine_negate_point_output ms bb (normalized_value byword)
   (point_canonical_limbs bxword) Int.zero (normalized_value_range byword)
   ltac:(rewrite point_canonical_limbs_length;lia) XBS YBS
   (OwnedS bb 88 ltac:(clear;cbn [linear_verify_arithmetic_storage In];tauto)) FlagBS)
  as (mn & Neg & XBN & YBN & FBN & FlagBN & FrameN).
 rewrite negate_reader_words in YBN.
 change (fe_at mn bb 40 (words5 (negate_sep_words (square_reader_rho byword)))) in YBN.
 rewrite rescale_reader_limbs in XBN.
 assert (FrameSN:lframe (fun b _=>b<>bz /\ b<>bb) m mn).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameS|intros b pos [NZ NB] Valid;exact NZ].
   - eapply lframe_implies;[exact FrameN|intros b pos [NZ NB] Valid;exact NB]. }
 assert (OwnedN:forall b hi,In (b,hi) (linear_verify_arithmetic_storage ba bb bk bg br bz) ->
  Mem.range_perm mn b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (peq b bb) as [Same|Different].
   - subst b;cbn [linear_verify_arithmetic_storage In] in Slot;
     repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
     inversion Slot;subst;try congruence;exact FBN.
   - eapply curve_keep_free;[|apply OwnedS;exact Slot|exact FrameN|intros;exact Different].
     cbn [linear_verify_arithmetic_storage In] in Slot;
     repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
     inversion Slot;subst;lia. }
 assert (XZN:fe_at mn bz 0 (words5 (square_reader_rho ax)))
  by (eapply field_at_lframe;[exact XZ|exact FrameN|intros;congruence]).
 assert (YZN:fe_at mn bz 40 (words5 (square_reader_rho ay)))
  by (eapply field_at_lframe;[exact YZ|exact FrameN|intros;congruence]).
 change (fe_at ms bz 80 (words5 (point_set_bit_words true))) in ZZ.
 assert (ZZN:fe_at mn bz 80 (words5 (point_set_bit_words true)))
  by (eapply field_at_lframe;[exact ZZ|exact FrameN|intros;congruence]).
 assert (ValidZ:Mem.valid_block ms bz) by (eapply Mem.perm_valid_block;apply (FZS 0);lia).
 assert (FlagZN:Mem.load Mint32 mn bz 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameN Mint32 bz 120 ValidZ ltac:(intros;congruence));exact FlagZ. }
 assert (InputN:scalar_at mn bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))))
  by (eapply scalar_at_lframe;[exact Input|exact FrameSN|intros;split;congruence]).
 assert (InputNGN:scalar_at mn bg 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)))))
  by (eapply scalar_at_lframe;[exact InputNG|exact FrameSN|intros;split;congruence]).
 assert (ReadS:readonly_preserved m ms).
 { eapply secp_closed_function_preserved;[exact (proj1 linear_verify_small_calls_closed)|reflexivity|exact SetCall]. }
 assert (ReadN:readonly_preserved ms mn).
 { eapply secp_closed_function_preserved;[exact (proj2 linear_verify_small_calls_closed)|reflexivity|exact Neg]. }
 assert (ReadyN:linear_startup mn).
 { eapply linear_startup_readonly;[exact Ready|eapply preserved_trans;[exact ReadS|exact ReadN]]. }
 assert (MultSeparate:NoDup [br;bk;bz;bg]).
 { clear -RZ KR GR KZ KG GZ;repeat constructor;cbn [In];intuition congruence. }
 assert (MultOwned:forall b hi,In (b,hi) [(br,128);(bk,32);(bz,128);(bg,32)] -> Mem.range_perm mn b 0 hi Cur Freeable).
 { intros b hi Slot;apply OwnedN;cbn [In] in Slot;cbn [linear_verify_arithmetic_storage In];tauto. }
 assert (OneFlag:Mem.load Mint32 mn bz 120=Some (Vint (bit_int (Bit.toBool
  (@literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)))))).
 { change (Mem.load Mint32 mn bz 120=Some (Vint (bit_int (Bit.toBool
    (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_one256 Alg.CoreFunSem tt)))))).
   rewrite literal_curve_zero_numeric,literal_fe_one256_value;exact FlagZN. }
 destruct (eval_ecmult_general_flag Model raw ng ax ay (@literal_fe_one256 Alg.CoreFunSem tt)
   (square_reader_rho ax) (square_reader_rho ay) (point_set_bit_words true) mn br bk bz bg
   (proj2 (proj2 ReadyN)) (proj1 ReadyN) (proj1 (proj2 ReadyN)) MultSeparate MultOwned InputN InputNGN
   (square_reader_bounds ax) (square_reader_bounds ay) mixed_one_bounds XZN YZN ZZN OneFlag
   (linear_verify_reader_residue ax) (linear_verify_reader_residue ay) linear_verify_one_residue)
  as (mm & ox & oy & oz & Mult & XM & YM & ZM & BOx & BOy & BOz & Literal & MultOwnedM & TablesM & FrameM & FlagM).
 specialize (FlagM (literal_affine_scalar_table_nonzero ax ay GuardA)).
 assert (OtherM:lframe (fun b _=>b=ba \/ b=bb) mn mm).
 { eapply lframe_implies;[exact FrameM|].
   intros b pos Member Valid;cbn [In];destruct Member as [SameA|SameB];subst b;intuition congruence. }
 assert (XBM:fe_at mm bb 0 (words5 (square_reader_rho bxword)))
  by (eapply field_at_lframe;[exact XBN|exact OtherM|intros;right;reflexivity]).
 assert (YBM:fe_at mm bb 40 (words5 (negate_sep_words (square_reader_rho byword))))
  by (eapply field_at_lframe;[exact YBN|exact OtherM|intros;right;reflexivity]).
 assert (ValidBN:Mem.valid_block mn bb) by (eapply Mem.perm_valid_block;apply (FBN 0);lia).
 assert (FlagBM:Mem.load Mint32 mm bb 80=Some (Vint Int.zero)).
 { rewrite (proj1 OtherM Mint32 bb 80 ValidBN ltac:(intros;right;reflexivity));exact FlagBN. }
 assert (FBM:Mem.range_perm mm bb 0 88 Cur Freeable)
  by (eapply curve_keep_free;[clear;lia|exact FBN|exact OtherM|intros;right;reflexivity]).
 destruct (eval_mixed_xy_literal_framed ox oy oz (square_reader_rho bxword)
   (negate_sep_words (square_reader_rho byword))
   (rescale_field_output ox) (rescale_field_output oy) (rescale_field_output oz)
   (rescale_field_output (square_reader_rho bxword))
   (rescale_field_output (negate_sep_words (square_reader_rho byword))) mm br bb
   (not_eq_sym BR) BOx BOy BOz (square_reader_bounds bxword) (linear_verify_negated_bounds byword)
   (mixed_xy_output_residue ox) (mixed_xy_output_residue oy) (mixed_xy_output_residue oz)
   (mixed_xy_output_residue _) (mixed_xy_output_residue _)
   FlagM FlagBM XM YM ZM XBM YBM
   (MultOwnedM br 128 ltac:(clear;cbn [In];tauto)) FBM)
  as (mf & fx & fy & fz & Add & XF & YF & ZF & FlagF & FRF & FBF & BFx & BFy & BFz & Result & Perm & ReadF & FrameF).
 rewrite mixed_reader_output,linear_verify_negated_output in Result.
 rewrite <-(linear_verify_negate_value bxword byword) in Result.
 rewrite Literal in Result.
 assert (ReadyM:linear_startup mm)
  by (eapply linear_startup_ecmult_call;[exact ReadyN|exact MultOwned|exact Mult|exact FrameM]).
 exists ms,mn,mm,mf;split;[exact SetCall|];split;[exact Neg|];split;[exact Mult|];split;[exact Add|];split.
 - eapply eq_trans;[exact FlagF|].
   exact (f_equal (fun p=>Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (snd p)))))) Result).
 - split.
   + intros b hi Slot;assert (Before:Mem.range_perm mm b 0 hi Cur Freeable).
     { destruct (peq b ba) as [->|NA];[|destruct (peq b bb) as [->|NB]].
     * assert (Size:hi=88).
       { cbn [linear_verify_arithmetic_storage In] in Slot;
         repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
         inversion Slot;subst;congruence. }
       subst hi;eapply curve_keep_free;[clear;lia|apply OwnedN;exact Slot|exact OtherM|intros;left;reflexivity].
     * assert (Size:hi=88).
       { cbn [linear_verify_arithmetic_storage In] in Slot;
         repeat match type of Slot with _\/_=>destruct Slot as [Slot|Slot] end;try contradiction;
         inversion Slot;subst;congruence. }
       subst hi;exact FBM.
     * apply MultOwnedM;clear -Slot NA NB;cbn [linear_verify_arithmetic_storage In] in Slot;
       cbn [In];intuition congruence. }
     intros pos Range;apply Perm;apply Before;exact Range.
   + split;[eapply linear_startup_readonly;[exact ReadyM|exact ReadF]|].
     eapply lframe_trans.
     * eapply lframe_implies;[exact FrameSN|].
       intros b pos NotLocal Valid;clear -NotLocal;cbn [In] in NotLocal;split;intuition congruence.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameM|].
          intros b pos NotLocal Valid;clear -NotLocal;cbn [In] in *;intuition congruence.
       -- eapply lframe_implies;[exact FrameF|].
          intros b pos NotLocal Valid;clear -NotLocal;cbn [In] in NotLocal;split;intuition congruence.
Qed.
