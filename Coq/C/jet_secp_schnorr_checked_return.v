(** Guarded original Schnorr suffix returns the canonical BIP340 predicate.
    Signature/key parsing and the outer public lifecycle are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import
 C.jet_readBit_layout C.jet_sx_mem C.jet_clight_forward
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_rescale_literal C.jet_secp_odd_table_literal_walk
 C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_generator_globals C.jet_secp_split_constants C.jet_secp_beta_global
 C.jet_secp_ecmult_general C.jet_secp_table_affine_nonzero C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_strauss_complete_program C.jet_secp_literal_gej_predicate
 C.jet_secp_even_x_test C.jet_secp_modinfo_fe_caller C.jet_ctz_model
 C.jet_memset_model C.jet_secp_root_chain_owned C.jet_secp_schnorr_after_mult
 C.jet_secp_scalar_table_literal C.jet_secp_canonical_zero C.jet_secp_field_read_preservation
 C.jet_secp_modinfo_fe_transport C.jet_secp_schnorr_mult_return C.jet_secp_literal_add_numeric
 C.jet_secp_generator_pair_general C.jet_secp_scalar_add_reader_support C.jet_clight_internal_frame
 C.jet_secp_gej_set_ge_owned C.jet_secp_closed_helpers C.jet_clight_internal_preserve
 C.jet_secp_generator_main C.jet_secp_point_set_bit C.jet_secp_beta_state.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_off_curve_linear_combination_1 literal_gej_is_infinity
 rescale_field_output literal_scalar_table5 canonical_fe_is_zero.
Require Import C.jet_secp_schnorr_gej_mult_return C.jet_secp_scalar_negate_canonical
 C.jet_secp_scalar_writer_storage C.jet_secp_scalar_writer_run C.jet_secp_scalar_reader_lifecycle
 C.jet_secp_scalar_negate_writer_identity C.jet_secp_canonical_scalar_negate
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_limb_bridge C.jet_toZ
 C.jet_word_repr C.jet_secp_scalar_read_write C.jet_sx_state C.jet_sx_rep.
Require Import C.jet_secp_schnorr_negate_return C.jet_secp_schnorr_challenge_literal
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb
 C.jet_secp_sha_startup C.jet_memcpy_model C.jet_secp_point_verify_literal
 C.jet_secp_schnorr_group_predicate.
Require Import C.jet_secp_schnorr_challenge_return C.jet_secp_schnorr_check_predicate
 C.jet_secp_schnorr_verify_literal C.jet_secp_decompress_literal C.jet_secp_canonical_normalize
 C.jet_secp_affine_word_valid.
Lemma schnorr_challenge_result_canonical (pk msg r s ax ay:Ty.tySem (Word 8)):
 @toZ (WordToZ 8) pk<feP ->@toZ (WordToZ 8) r<feP ->@toZ (WordToZ 8) s<canonical_group_order ->
 @literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 secp_even_x_test (@literal_off_curve_linear_combination_1 Simplicity.Alg.CoreFunSem
  ((@canonical_scalar_negate Simplicity.Alg.CoreFunSem
    (@literal_bip0340_challenge Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))),
   ((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)),s)) r=
 Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))).
Proof.
 intros PK R S Decode;rewrite secp_schnorr_check_predicate;unfold secp_schnorr_check_test.
 rewrite (proj2 (Z.ltb_lt _ _) PK),(proj2 (Z.ltb_lt _ _) R),(proj2 (Z.ltb_lt _ _) S).
 cbn [andb];rewrite Decode,literal_bip0340_challenge_value;reflexivity.
Qed.
Theorem exec_schnorr_challenge_return_canonical (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 e le m bp bk ba bng br bx bpk x y rv (ng ax ay r pk msg:Ty.tySem (Word 8))
 bsig osig bmsg omsg bbuf:
 e!_buf=Some (bbuf,tarray tuchar 32) ->e!_secp256k1_schnorrsig_challenge=None ->
 le!_sig64=Some (Vptr bsig osig) ->le!_msg=Some (Vptr bmsg omsg) ->le!_msglen=Some (Vlong (Int64.repr 32)) ->
 Ptrofs.unsigned osig+32<=Ptrofs.max_unsigned ->Ptrofs.unsigned omsg+32<=Ptrofs.max_unsigned ->
 schnorr_bytes_at m bsig osig (schnorr_word_bytes r) ->
 schnorr_bytes_at m bbuf Ptrofs.zero (schnorr_word_bytes pk) ->
 schnorr_bytes_at m bmsg omsg (schnorr_word_bytes msg) ->secp_sha_startup m ->
 e!_secp256k1_scalar_negate=None ->
 e!_pk=Some (bpk,curve_ge_type) ->e!_secp256k1_gej_set_ge=None ->
 e!_rj=Some (bp,Tstruct __6123 noattr) ->e!_pkj=Some (ba,Tstruct __6123 noattr) ->
 e!_e=Some (bk,Tstruct __5826 noattr) ->e!_s=Some (bng,Tstruct __5826 noattr) ->
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_ecmult=None ->e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_ge_is_infinity=None ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 NoDup [bp;bk;ba;bng;br;bx;bpk] ->
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds x ->square_input_bounds y ->
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m bpk 0 (words5 x) ->fe_at m bpk 40 (words5 y) ->Mem.load Mint32 m bpk 80=Some (Vint Int.zero) ->fe_at m bx 0 (words5 rv) ->
 table_word_literal x ax ->table_word_literal y ay ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 @toZ (WordToZ 8) pk<feP ->@toZ (WordToZ 8) r<feP ->@toZ (WordToZ 8) ng<canonical_group_order ->
 @literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_challenge_return E0 lef mf
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))))),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk]) m mf /\mem_forward m mf.
Proof.
 intros Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound RBytes PKBytes MsgBytes Startup
  NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate Owned Tables Split Beta Ready
  InputNG BX BY BR X Y KeyFlag RV TX TY TR PKBound RBound SBound Decode.
 pose proof (secp_decompress_curve pk (inl tt) (ax,ay) Decode) as ValidCurve.
 destruct (exec_schnorr_challenge_return_owned Copy Clear Count e le m bp bk ba bng br bx bpk x y rv
  ng ax ay r pk msg bsig osig bmsg omsg bbuf Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound
  RBytes PKBytes MsgBytes Startup NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate Owned
  Tables Split Beta Ready InputNG BX BY BR X Y KeyFlag RV TX TY TR ValidCurve)
 as (mf & lef & Exec & OwnedF & FrameF & ForwardF).
 exists mf,lef;split.
 - rewrite (schnorr_challenge_result_canonical pk msg r ng ax ay PKBound RBound SBound Decode) in Exec;exact Exec.
 - repeat first [assumption|split].
Qed.
