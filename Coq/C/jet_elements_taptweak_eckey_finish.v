(** Real linked tweak infinity guard and finite affine return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
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
Require Import C.jet_secp_eckey_tweak_finish C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals
 C.jet_elements_taptweak_modinfo C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_load_body
 C.jet_elements_taptweak_parse_start.
Require Import C.jet_elements_taptweak_affine_finite.
Lemma elements_taptweak_has_gej_is_infinity:
 In(_secp256k1_gej_is_infinity,f_secp256k1_gej_is_infinity)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_gej_is_infinity)elements_taptweak_curve_helpers=
 Some(_secp256k1_gej_is_infinity,f_secp256k1_gej_is_infinity))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Lemma elements_taptweak_affine_helper_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_ge_set_gej_var=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_ge_set_gej_var).
Proof. exists(elements_taptweak_symbol_block _secp256k1_ge_set_gej_var);split;vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers point_mul_words square_words rescale_field_output literal_gej_norm.
Lemma exec_elements_taptweak_eckey_guard e le m bp infinite:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->e!_secp256k1_gej_is_infinity=None ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int infinite)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m eckey_tweak_guard E0
 (PTree.set _t'1 (Vint (bit_int infinite)) le) m
 (if infinite then Out_return (Some (Vint Int.zero,tint)) else Out_normal).
Proof.
 intros Point Symbol Flag;unfold eckey_tweak_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
 (m1:=m) (le1:=PTree.set _t'1 (Vint (bit_int infinite)) le).
 - eapply exec_elements_taptweak_arith_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vint (bit_int infinite)).
   + exact elements_taptweak_has_gej_is_infinity.
   + exact Symbol.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Point|reflexivity|constructor].
   + eapply elements_taptweak_curve_transport;[exact elements_taptweak_has_gej_is_infinity|].
     apply eval_gej_flag_accessor;[lia|change(128<=18446744073709551615);lia|exact Flag].
 - destruct infinite.
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|apply exec_Sreturn_some;constructor].
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|constructor].
Qed.
Lemma exec_elements_taptweak_eckey_affine e le m mf bp bk:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->le!_key=Some (Vptr bk Ptrofs.zero) ->
 e!_secp256k1_ge_set_gej_var=None ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ge_set_gej_var) [Vptr bk Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge e le m eckey_tweak_affine E0 le mf Out_normal.
Proof.
 intros Point Key Symbol Call;destruct elements_taptweak_affine_helper_linked as(bf & Named & Funct).
 unfold eckey_tweak_affine;eapply exec_elements_taptweak_curve_call with(bf:=bf)
 (vargs:=[Vptr bk Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
 - exact Named.
 - unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Etempvar;exact Key|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Point|reflexivity|constructor].
 - exact Call.
Qed.
Theorem exec_elements_taptweak_eckey_finish (Model:ctz_model) e le m bp bk x y z infinite:
 e!_pt=Some (bp,Tstruct __6123 noattr) ->le!_key=Some (Vptr bk Ptrofs.zero) ->
 e!_secp256k1_gej_is_infinity=None ->e!_secp256k1_ge_set_gej_var=None ->bp<>bk ->
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int infinite)) ->elements_taptweak_modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m bk 0 88 Cur Freeable ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m eckey_tweak_finish E0
 (PTree.set _t'1 (Vint (bit_int infinite)) le) mf
 (Out_return (Some (Vint (bit_int (negb infinite)),tint))) /\
 eckey_tweak_affine_result infinite x y z mf bk /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf bk 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bp /\b<>bk) m mf /\readonly_preserved m mf.
Proof.
 intros Point Key InfinitySym ConvertSym Separate BX BY BZ X Y Z Flag Ready FP FK.
 pose proof (exec_elements_taptweak_eckey_guard e le m bp infinite Point InfinitySym Flag) as Guard.
 destruct infinite.
 - exists m;split.
   + unfold eckey_tweak_finish;eapply exec_Sseq_2;[exact Guard|clear;discriminate].
   + split;[intro Impossible;discriminate Impossible|];split;[exact FP|];split;[exact FK|];
     split;[apply lframe_refl|apply preserved_refl].
 - destruct (eval_elements_taptweak_affine_finite Model x y z m bp bk
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
     * eapply exec_elements_taptweak_eckey_affine;[exact Point| |exact ConvertSym|exact Convert].
       rewrite PTree.gso by discriminate;exact Key.
     * apply exec_Sreturn_some;constructor.
   + split.
     * intros _;exists (point_mul_words x (square_words zi)),(point_mul_words y (point_mul_words zi (square_words zi)));
       split;[exact XO|];split;[exact YO|];split;[exact BXO|];split;[exact BYO|];split;[exact FlagF|exact Literal].
     * split;[exact FPF|];split;[exact FKF|];split;[exact Frame|exact Read].
Qed.
