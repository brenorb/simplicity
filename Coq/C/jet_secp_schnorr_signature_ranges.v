(** All original signature parsing outcomes through the frozen BIP340 return. *)
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
Require Import C.jet_secp_schnorr_checked_return C.jet_secp_b32_owned C.jet_secp_b32_exec
 C.jet_secp_multiply_input_input C.jet_secp_even_decompress.
Require Import C.jet_secp_word_bytes_codec.
Require Import C.jet_secp_schnorr_serialize_return C.jet_secp_pubkey_load_coordinates
 C.jet_secp_affine_storage C.jet_secp_storage_numeric.
Require Import C.jet_secp_statement_prefix C.jet_read8s_layout C.jet_secp_schnorr_signature_read C.jet_secp_schnorr_r_read C.jet_secp_schnorr_scalar_read C.jet_secp_xonly_parse_field C.jet_secp_schnorr_keyload_return C.jet_secp_table_decode C.jet_clight_internal_permissions.
Require Import C.jet_secp_schnorr_signature_return C.jet_secp_schnorr_signature_guards C.jet_secp_set_b32_owned_frame C.jet_secp_scalar_set_flag.
Theorem exec_schnorr_signature_return_all (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 w e le m bp bk ba bng br bx bpk bf (ng ax ay r pk msg:Ty.tySem (Word 8))
 bsig bmsg omsg bbuf bkey keybase:
 e!_secp256k1_xonly_pubkey_load=None ->
 le!_pubkey=Some (Vptr bkey (Ptrofs.repr keybase)) ->
 affine_storage_readable m bkey keybase w ->
 field_storage_value w=@toZ (WordToZ 8) pk ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 e!_secp256k1_fe_get_b32=None ->
 e!_buf=Some (bbuf,tarray tuchar 32) ->e!_secp256k1_schnorrsig_challenge=None ->
 le!_sig64=Some (Vptr bsig Ptrofs.zero) ->le!_msg=Some (Vptr bmsg omsg) ->le!_msglen=Some (Vlong (Int64.repr 32)) ->
 Ptrofs.unsigned omsg+32<=Ptrofs.max_unsigned ->
 e!_overflow=Some (bf,tint) ->e!_secp256k1_fe_set_b32=None ->e!_secp256k1_scalar_set_b32=None ->
 Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes ng)) ->
 schnorr_bytes_at m bmsg omsg (schnorr_word_bytes msg) ->secp_sha_startup m ->
 e!_secp256k1_scalar_negate=None ->
 e!_pk=Some (bpk,curve_ge_type) ->e!_secp256k1_gej_set_ge=None ->
 e!_rj=Some (bp,Tstruct __6123 noattr) ->e!_pkj=Some (ba,Tstruct __6123 noattr) ->
 e!_e=Some (bk,Tstruct __5826 noattr) ->e!_s=Some (bng,Tstruct __5826 noattr) ->
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_ecmult=None ->e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_ge_is_infinity=None ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 NoDup [bp;bk;ba;bng;br;bx;bpk;bbuf;bf] ->
 ~In bsig [bp;bk;ba;bng;br;bx;bpk;bbuf;bf] ->~In bmsg [bbuf;bpk] ->
 ~In bmsg [bx;bng;bf;bsig] ->~In bkey [bx;bng;bf;bsig] ->
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32);(bf,4)] ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 @toZ (WordToZ 8) pk<feP ->
 @literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_drop_statements 3 (fn_body f_secp256k1_schnorrsig_verify)) E0 lef mf
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))))),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32);(bf,4)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 Mem.range_perm mf bsig 0 64 Cur Freeable /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk;bbuf;bf;bsig]) m mf /\mem_forward m mf.
Proof.
 intros LoadSym KeyPtr KeyInput KeyX KeyY SerializeSym Buf ChallengeSym Sig Msg MsgLen MsgBound
  Flag ReadSym ScalarSym SigFree RInput SInput MsgBytes Startup NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES
  Separate SigSep MsgSep MsgReadSep KeyReadSep Owned Tables Split Beta Ready PKBound Decode.
 assert (Pairs:bx<>bsig /\bng<>bsig /\bf<>bng /\bf<>bsig).
 { clear -Separate SigSep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;intuition congruence. }
 destruct Pairs as (XI & SI & FS & FI).
 destruct (Z_lt_ge_dec (@toZ (WordToZ 8) r) feP) as [RBound|RHigh].
 - destruct (Z_lt_ge_dec (@toZ (WordToZ 8) ng) canonical_group_order) as [SBound|SHigh].
   + exact (exec_schnorr_signature_return_canonical Copy Clear Count w e le m bp bk ba bng br bx bpk bf
     ng ax ay r pk msg bsig bmsg omsg bbuf bkey keybase
     LoadSym KeyPtr KeyInput KeyX KeyY SerializeSym Buf ChallengeSym Sig Msg MsgLen MsgBound
     Flag ReadSym ScalarSym SigFree RInput SInput MsgBytes Startup NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES
     Separate SigSep MsgSep MsgReadSep KeyReadSep Owned Tables Split Beta Ready PKBound RBound SBound Decode).
   + destruct (exec_schnorr_r_read r (map Int.repr (xonly_input_bytes ng)) e le m bx bsig RX ReadSym Sig XI
     (Owned bx 40 ltac:(clear;cbn [In];tauto)) SigFree RInput
     ltac:(rewrite map_length,xonly_input_length;clear;lia) SInput)
     as (mr & RRead & RV & RBytes & SBytes & KeepR & FrameR & ReadR).
     assert (SigR:(schnorr_r_read_temps le r)!_sig64=Some (Vptr bsig Ptrofs.zero)).
     { unfold schnorr_r_read_temps;rewrite PTree.gso by (clear;discriminate);exact Sig. }
     destruct (exec_schnorr_scalar_reject pk msg r ng e (schnorr_r_read_temps le r) mr bng bsig bf
      ltac:(lia) S Flag ScalarSym SigR SI FS FI
      ltac:(intros pos Range;apply KeepR;apply (Owned bng 32);[clear;cbn [In];tauto|exact Range])
      ltac:(intros pos Range;apply KeepR,SigFree;exact Range)
      ltac:(intros pos Range;apply KeepR;apply (Owned bf 4);[clear;cbn [In];tauto|exact Range]) SBytes)
     as (mf & lef & Reject & Spec & KeepS & FrameS & ReadS).
     assert (InRange:Z.ltb (@toZ (WordToZ 8) r) feP=true) by (apply Z.ltb_lt;exact RBound).
     unfold schnorr_r_read_outcome in RRead;rewrite InRange in RRead.
     exists mf,lef;split.
     * rewrite Spec,schnorr_r_read_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact RRead|exact Reject].
     * split.
       -- intros b hi Slot pos Range;apply KeepS,KeepR;apply (Owned b hi Slot pos Range).
       -- split;[intros pos Range;apply KeepS,KeepR,SigFree;exact Range|].
          split.
          ++ eapply lframe_trans.
             ** eapply lframe_implies;[exact FrameR|].
                intros b pos Outside _ Foot;destruct (owned_b32_foot_bounds bx bsig b pos Foot)
                 as [[Same _]|[Same _]];clear -Outside Same;cbn [In] in *;intuition congruence.
             ** eapply lframe_implies;[exact FrameS|].
                intros b pos Outside _;assert (Pairs:b<>bng /\b<>bsig /\b<>bf)
                 by (clear -Outside;cbn [In] in *;intuition congruence).
                split;[apply scalar_flag_foot_outside;exact Pairs|exact (proj2 (proj2 Pairs))].
          ++ eapply mem_forward_trans;[exact (proj1 ReadR)|exact (proj1 ReadS)].
 - destruct (exec_schnorr_r_reject pk msg r ng e le m bx bsig ltac:(lia) RX ReadSym Sig XI
    (Owned bx 40 ltac:(clear;cbn [In];tauto)) SigFree RInput)
   as (mf & lef & Reject & Spec & Keep & Frame & Read).
   exists mf,lef;split.
   + rewrite Spec;exact Reject.
   + split.
     * intros b hi Slot pos Range;apply Keep;apply (Owned b hi Slot pos Range).
     * split;[intros pos Range;apply Keep,SigFree;exact Range|].
       split.
       -- eapply lframe_implies;[exact Frame|].
          intros b pos Outside _ Foot;destruct (owned_b32_foot_bounds bx bsig b pos Foot)
           as [[Same _]|[Same _]];clear -Outside Same;cbn [In] in *;intuition congruence.
       -- exact (proj1 Read).
Qed.
