(** Original verifier suffix from the multiplier output to its return value. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.extraMath C.jet_readBit_layout C.jet_sx_mem C.jet_ctz_model C.jet_secp_ctz_external_call
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_clight_internal_preserve C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_numeric
 C.jet_secp_point_mul_storage C.jet_secp_generator_finish C.jet_secp_fe_inverse_state
 C.jet_secp_fe_inv_prefix C.jet_secp_invert_literal C.jet_secp_modinfo_fe_caller
 C.jet_secp_gej_norm_output C.jet_secp_affine_inverse_literal C.jet_secp_affine_flag_read
 C.jet_secp_schnorr_return_control C.jet_secp_schnorr_return_owned C.jet_secp_root_chain_owned
 C.jet_secp_odd_table_literal_walk C.jet_secp_globalz_word_walk C.jet_secp_rescale_literal C.jet_secp_canonical_odd
 C.jet_secp_literal_gej_predicate C.jet_secp_gej_norm_literal C.jet_secp_even_x_test.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_norm literal_gej_is_infinity rescale_field_output
 canonical_fe_is_odd point_mul_words square_words.
Definition schnorr_after_mult_convert:=curve_call _secp256k1_ge_set_gej_var f_secp256k1_ge_set_gej_var None
 [Eaddrof (Evar _r curve_ge_type) (tptr curve_ge_type);
  Eaddrof (Evar _rj (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition schnorr_after_mult_flag:=curve_call _secp256k1_ge_is_infinity f_secp256k1_ge_is_infinity (Some _t'4)
 [Eaddrof (Evar _r curve_ge_type) (tptr curve_ge_type)].
Definition schnorr_after_mult_guard:=Ssequence schnorr_after_mult_flag
 (Sifthenelse (Etempvar _t'4 tint) (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition schnorr_after_mult_tail:=Ssequence schnorr_after_mult_convert
 (Ssequence schnorr_after_mult_guard schnorr_return_tail).
Lemma schnorr_after_mult_source:root_drop_statements 12 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_after_mult_tail.
Proof. reflexivity. Qed.
Lemma exec_schnorr_conversion e le m ma bp br:
 e!_r=Some (br,curve_ge_type) ->e!_rj=Some (bp,Tstruct __6123 noattr) ->
 e!_secp256k1_ge_set_gej_var=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 ma Vundef ->
 Clight2.exec_stmt secp_ge e le m schnorr_after_mult_convert E0 le ma Out_normal.
Proof.
 intros R RJ Symbol Call;unfold schnorr_after_mult_convert;eapply exec_curve_call with
  (vargs:=[Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact R|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact RJ|reflexivity|constructor].
 - exact Call.
Qed.
Lemma exec_schnorr_result_flag e le m br flag:
 e!_r=Some (br,curve_ge_type) ->e!_secp256k1_ge_is_infinity=None ->
 Mem.load Mint32 m br 80=Some (Vint flag) ->
 Clight2.exec_stmt secp_ge e le m schnorr_after_mult_flag E0
 (PTree.set _t'4 (Vint flag) le) m Out_normal.
Proof.
 intros R Symbol Flag;unfold schnorr_after_mult_flag;eapply exec_curve_call with
  (vargs:=[Vptr br Ptrofs.zero]) (v:=Vint flag).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact R|reflexivity|constructor].
 - exact (eval_affine_flag_accessor m br 0 flag ltac:(lia)
   ltac:(change (88<=18446744073709551615);lia) Flag).
Qed.
Theorem exec_schnorr_after_mult_owned (Model:ctz_model) e le m bp br bx x y z rv
 (a b c r:Ty.tySem (Word 8)):
 e!_r=Some (br,curve_ge_type) ->e!_rj=Some (bp,Tstruct __6123 noattr) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_ge_is_infinity=None ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 bp<>br ->bp<>bx ->br<>bx ->square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->fe_at m bx 0 (words5 rv) ->
 table_word_literal x a ->table_word_literal y b ->table_word_literal z c ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem ((a,b),c))))) ->modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bx 0 40 Cur Freeable ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_after_mult_tail E0 lef mf
  (Out_return (Some (Vint (bit_int (secp_even_x_test ((a,b),c) r)),tint))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bx 0 40 Cur Freeable /\
 lframe (fun block _=>block<>bp /\block<>br /\block<>bx) m mf /\readonly_preserved m mf.
Proof.
 intros R RJ RX CS IS NS OS ES PR PX RXSep BX BY BZ BR X Y Z RV TX TY TZ TR Flag Ready FP FR FX.
 set (infinite:=Simplicity.Bit.toBool (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem ((a,b),c))).
 fold infinite in Flag.
 destruct (eval_generator_affine_all x y z (bit_int infinite) m bp br ltac:(intros mc w Nonzero;apply eval_ctz64_from_external;exact (Model _ mc w Nonzero))
  PR BX BY BZ X Y Z Flag Ready FP FR)
 as (ma & ox & oy & Convert & XA & YA & AffineFlag & BXA & BYA & Finite & Infinite & FPA & FRA & FrameA & ReadA).
 assert (RVA:fe_at ma bx 0 (words5 rv)).
 { eapply curve_keep_field_range;[reflexivity|exact RV|exact FrameA|];intros;split;congruence. }
 assert (FXA:Mem.range_perm ma bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FX|exact FrameA|];intros;split;congruence. }
 assert (Conversion:Clight2.exec_stmt secp_ge e le m schnorr_after_mult_convert E0 le ma Out_normal)
 by (apply (exec_schnorr_conversion e le m ma bp br R RJ CS Convert)).
 destruct infinite eqn:Infinity.
 - cbn [bit_int] in AffineFlag;change (Mem.load Mint32 ma br 80=Some (Vint Int.one)) in AffineFlag.
   assert (Expected:secp_even_x_test ((a,b),c) r=false).
   { unfold secp_even_x_test;fold infinite;rewrite Infinity;reflexivity. }
   exists ma,(PTree.set _t'4 (Vint Int.one) le);rewrite Expected.
   split.
   + unfold schnorr_after_mult_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=le);[exact Conversion|].
     eapply exec_Sseq_2 with (t1:=E0);[|discriminate].
     unfold schnorr_after_mult_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma)
      (le1:=PTree.set _t'4 (Vint Int.one) le).
     * apply exec_schnorr_result_flag with (br:=br);assumption.
     * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
       { apply eval_Etempvar;apply PTree.gss. }
       { reflexivity. }
       apply exec_Sreturn_some;constructor.
   + split;[exact FPA|];split;[exact FRA|];split;[exact FXA|];split;[|exact ReadA].
     eapply lframe_implies;[exact FrameA|];intros block pos [NP [NR NX]] Valid;split;assumption.
 - cbn [bit_int] in AffineFlag;change (Mem.load Mint32 ma br 80=Some (Vint Int.zero)) in AffineFlag.
   destruct (Finite eq_refl) as (zi & Inverse & OX & OY & VX & VY).
   assert (IZ:radix_value zi mod feP=literal_invert_numeric (@toZ (WordToZ 8) c) mod feP).
   { rewrite Inverse;unfold fe_inv_value;rewrite TZ,literal_invert_numeric_mod_field by apply word_toZ_range;reflexivity. }
   assert (Literal:(rescale_field_output ox,rescale_field_output oy)=
    @literal_gej_norm Simplicity.Alg.CoreFunSem ((a,b),c)).
   { eapply affine_normalized_words_literal;[exact TX|exact TY|exact IZ| |];
     rewrite field_prime_matches_normalizer;assumption. }
   set (odd:=Simplicity.Bit.toBool (@canonical_fe_is_odd Simplicity.Alg.CoreFunSem (rescale_field_output oy))).
   set (equal:=Z.eqb (radix_value rv mod feP) (radix_value ox mod feP)).
   assert (Expected:secp_even_x_test ((a,b),c) r=andb (negb odd) equal).
   { unfold secp_even_x_test;fold infinite;rewrite Infinity,<-Literal;cbn [fst snd].
     unfold odd,equal;rewrite rescale_field_output_value,field_prime_matches_normalizer,TR,Z.eqb_sym;reflexivity. }
   pose (li:=PTree.set _t'4 (Vint Int.zero) le).
   destruct (exec_schnorr_return_owned e li ma br bx ox oy rv R RX NS OS ES RXSep BXA BYA BR XA YA RVA FRA FXA)
    as (mf & Return & FRF & FXF & FrameR & ReadR).
   exists mf,(schnorr_return_temps li odd equal);rewrite Expected.
   split.
   + unfold schnorr_after_mult_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=le);[exact Conversion|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=li);[|exact Return].
     unfold schnorr_after_mult_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=li).
     * apply exec_schnorr_result_flag with (br:=br);assumption.
     * eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
       { apply eval_Etempvar;apply PTree.gss. }
       { reflexivity. }
       apply exec_Sskip.
   + split.
     * eapply curve_keep_free;[lia|exact FPA|exact FrameR|];intros;split;congruence.
     * split;[exact FRF|];split;[exact FXF|];split.
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameA|];intros block pos [NP [NR NX]] Valid;split;assumption.
         - eapply lframe_implies;[exact FrameR|];intros block pos [NP [NR NX]] Valid;split;assumption. }
       eapply preserved_trans;[exact ReadA|exact ReadR].
Qed.
