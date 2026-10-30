(** Actual infinity guard and affine return of the native public-key tweak. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_eckey_tweak_entry C.jet_secp_gej_flag_read C.jet_secp_affine_inverse_complete
 C.jet_secp_affine_inverse_literal C.jet_secp_gej_norm_output C.jet_secp_gej_norm_literal
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_point_mul_storage C.jet_secp_rescale_literal C.jet_secp_fe_inverse_state
 C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix C.jet_secp_modinfo_fe_caller
 C.jet_ctz_model C.jet_secp_ctz_external_call C.jet_readBit_layout C.jet_sx_mem
 C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words rescale_field_output literal_gej_norm.
Lemma exec_eckey_tweak_guard e le m bp infinite:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->e!_secp256k1_gej_is_infinity=None ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int infinite)) ->
 Clight2.exec_stmt secp_ge e le m eckey_tweak_guard E0
 (PTree.set _t'1 (Vint (bit_int infinite)) le) m
 (if infinite then Out_return (Some (Vint Int.zero,tint)) else Out_normal).
Proof.
 intros Point Symbol Flag;unfold eckey_tweak_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
 (m1:=m) (le1:=PTree.set _t'1 (Vint (bit_int infinite)) le).
 - eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vint (bit_int infinite)).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact Symbol.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Point|reflexivity|constructor].
   + apply eval_gej_flag_accessor;[lia|change (128<=18446744073709551615);lia|exact Flag].
 - destruct infinite.
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|apply exec_Sreturn_some;constructor].
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|constructor].
Qed.
Lemma exec_eckey_tweak_affine e le m mf bp bk:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->le!_key=Some (Vptr bk Ptrofs.zero) ->
 e!_secp256k1_ge_set_gej_var=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var) [Vptr bk Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m eckey_tweak_affine E0 le mf Out_normal.
Proof.
 intros Point Key Symbol Call;unfold eckey_tweak_affine;eapply exec_curve_call with
 (vargs:=[Vptr bk Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Etempvar;exact Key|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Point|reflexivity|constructor].
 - exact Call.
Qed.
Definition eckey_tweak_affine_result infinite x y z m bk:Prop:=infinite=false ->exists ox oy,
 fe_at m bk 0 (words5 ox) /\fe_at m bk 40 (words5 oy) /\
 square_input_bounds ox /\square_input_bounds oy /\Mem.load Mint32 m bk 80=Some (Vint Int.zero) /\
 (rescale_field_output ox,rescale_field_output oy)=
 @literal_gej_norm Simplicity.Alg.CoreFunSem ((rescale_field_output x,rescale_field_output y),rescale_field_output z).
Theorem exec_eckey_tweak_finish (Model:ctz_model) e le m bp bk x y z infinite:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->le!_key=Some (Vptr bk Ptrofs.zero) ->
 e!_secp256k1_gej_is_infinity=None ->e!_secp256k1_ge_set_gej_var=None ->bp<>bk ->
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int infinite)) ->modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m bk 0 88 Cur Freeable ->exists mf,
 Clight2.exec_stmt secp_ge e le m eckey_tweak_finish E0
 (PTree.set _t'1 (Vint (bit_int infinite)) le) mf
 (Out_return (Some (Vint (bit_int (negb infinite)),tint))) /\
 eckey_tweak_affine_result infinite x y z mf bk /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf bk 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bp /\b<>bk) m mf /\readonly_preserved m mf.
Proof.
 intros Point Key InfinitySym ConvertSym Separate BX BY BZ X Y Z Flag Ready FP FK.
 pose proof (exec_eckey_tweak_guard e le m bp infinite Point InfinitySym Flag) as Guard.
 destruct infinite.
 - exists m;split.
   + unfold eckey_tweak_finish;eapply exec_Sseq_2;[exact Guard|clear;discriminate].
   + split;[intro Impossible;discriminate Impossible|];split;[exact FP|];split;[exact FK|];
     split;[apply lframe_refl|apply preserved_refl].
 - destruct (eval_affine_finite_initialized x y z m bp bk
   ltac:(intros mc w Nonzero;apply eval_ctz64_from_external;exact (Model _ mc w Nonzero))
   Separate BX BY BZ X Y Z Flag Ready FP FK)
   as (zi & mf & Convert & XO & YO & FlagF & FPF & FKF & BXO & BYO & Inverse & VX & VY & ReadyF & Frame & Read).
   assert (Inv:radix_value zi mod feP=literal_invert_numeric (@toZ (WordToZ 8) (rescale_field_output z)) mod feP).
   { rewrite Inverse,rescale_field_output_value,field_prime_matches_normalizer;reflexivity. }
   assert (Literal:
    (rescale_field_output (point_mul_words x (square_words zi)),
     rescale_field_output (point_mul_words y (point_mul_words zi (square_words zi))))=
    @literal_gej_norm Simplicity.Alg.CoreFunSem ((rescale_field_output x,rescale_field_output y),rescale_field_output z)).
   { eapply affine_normalized_words_literal;[| |exact Inv|exact VX|exact VY];
     rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
   exists mf;split.
   + unfold eckey_tweak_finish;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=PTree.set _t'1 (Vint Int.zero) le);[exact Guard|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint Int.zero) le).
     * eapply exec_eckey_tweak_affine;[exact Point| |exact ConvertSym|exact Convert].
       rewrite PTree.gso by discriminate;exact Key.
     * apply exec_Sreturn_some;constructor.
   + split.
     * intros _;exists (point_mul_words x (square_words zi)),(point_mul_words y (point_mul_words zi (square_words zi)));
       split;[exact XO|];split;[exact YO|];split;[exact BXO|];split;[exact BYO|];split;[exact FlagF|exact Literal].
     * split;[exact FPF|];split;[exact FKF|];split;[exact Frame|exact Read].
Qed.
