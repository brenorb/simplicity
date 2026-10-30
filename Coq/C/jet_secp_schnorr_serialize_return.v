(** Actual key-X serialization and canonical Schnorr challenge-to-return suffix. *)
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
Definition schnorr_key_x_address:=Eaddrof
 (Efield (Evar _pk curve_ge_type) _x curve_fe_type) (tptr curve_fe_type).
Definition schnorr_serialize_call:=curve_call _secp256k1_fe_get_b32 f_secp256k1_fe_get_b32 None
 [Evar _buf (tarray tuchar 32);schnorr_key_x_address].
Definition schnorr_serialize_return:=Ssequence schnorr_serialize_call schnorr_challenge_return.
Lemma schnorr_serialize_return_source:
 root_drop_statements 7 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_serialize_return.
Proof. reflexivity. Qed.
Lemma eval_schnorr_key_x_address e le m bpk:
 e!_pk=Some (bpk,curve_ge_type) ->
 eval_expr secp_ge e le m schnorr_key_x_address (Vptr bpk Ptrofs.zero).
Proof.
 intro LocalPK.
 destruct (curve_affine_layout _x 0 ltac:(left;reflexivity)) as (co & Layout & Offset).
 apply eval_Eaddrof;unfold schnorr_key_x_address.
 rewrite <- (Ptrofs.add_zero_l Ptrofs.zero).
 eapply eval_Efield_struct with (co:=co) (delta:=0).
 - eapply eval_Elvalue;[apply eval_Evar_local;exact LocalPK|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Layout.
 - exact Offset.
Qed.
Theorem exec_schnorr_serialize_return_canonical (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 e le m bp bk ba bng br bx bpk y rv (ng ax ay r pk msg:Ty.tySem (Word 8))
 bsig osig bmsg omsg bbuf:
 e!_secp256k1_fe_get_b32=None ->
 e!_buf=Some (bbuf,tarray tuchar 32) ->e!_secp256k1_schnorrsig_challenge=None ->
 le!_sig64=Some (Vptr bsig osig) ->le!_msg=Some (Vptr bmsg omsg) ->le!_msglen=Some (Vlong (Int64.repr 32)) ->
 Ptrofs.unsigned osig+32<=Ptrofs.max_unsigned ->Ptrofs.unsigned omsg+32<=Ptrofs.max_unsigned ->
 schnorr_bytes_at m bsig osig (schnorr_word_bytes r) ->
 schnorr_bytes_at m bmsg omsg (schnorr_word_bytes msg) ->secp_sha_startup m ->
 e!_secp256k1_scalar_negate=None ->
 e!_pk=Some (bpk,curve_ge_type) ->e!_secp256k1_gej_set_ge=None ->
 e!_rj=Some (bp,Tstruct __6123 noattr) ->e!_pkj=Some (ba,Tstruct __6123 noattr) ->
 e!_e=Some (bk,Tstruct __5826 noattr) ->e!_s=Some (bng,Tstruct __5826 noattr) ->
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_ecmult=None ->e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_ge_is_infinity=None ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 NoDup [bp;bk;ba;bng;br;bx;bpk;bbuf] ->
 ~In bsig [bbuf;bpk] ->~In bmsg [bbuf;bpk] ->
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32)] ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds y ->
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m bpk 0 (map Int64.repr (fe_limbs_of (@toZ (WordToZ 8) pk))) ->fe_at m bpk 40 (words5 y) ->Mem.load Mint32 m bpk 80=Some (Vint Int.zero) ->fe_at m bx 0 (words5 rv) ->
 table_word_literal y ay ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 @toZ (WordToZ 8) pk<feP ->@toZ (WordToZ 8) r<feP ->@toZ (WordToZ 8) ng<canonical_group_order ->
 @literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_serialize_return E0 lef mf
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))))),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk;bbuf]) m mf /\mem_forward m mf.
Proof.
 intros SerializeSym Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound RBytes MsgBytes Startup
  NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate SigSep MsgSep Owned Tables Split Beta Ready
  InputNG BY BR X Y KeyFlag RV TY TR PKBound RBound SBound Decode.
 pose (value:=@toZ (WordToZ 8) pk).
 assert (Range:0<=value<2^256) by (apply word_toZ_range).
 assert (Different:bbuf<>bpk).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct (eval_fe_get_b32_owned m bbuf 0 bpk 0 value Range ltac:(clear;lia)
  ltac:(change (32<=18446744073709551615);lia)
  (Owned bbuf 32 ltac:(clear;cbn [In];tauto)) X Different)
 as (mi & Serialize & Bytes & XI & Keep & FrameI & ReadI).
 assert (BlockFrame:lframe (fun b _=>b<>bbuf /\b<>bpk) m mi).
 { eapply lframe_implies;[exact FrameI|];intros b pos [NB NP] _ Foot.
   destruct (get_b32_foot_bounds bbuf 0 bpk 0 b pos Foot) as [[Same _]|[Same _]];congruence. }
 assert (KeyBytes:schnorr_bytes_at mi bbuf Ptrofs.zero (schnorr_word_bytes pk)).
 { unfold value in Bytes;rewrite word256_serializer_bytes in Bytes.
   intros i Index;rewrite Ptrofs.unsigned_zero,Z.add_0_l.
   apply Bytes;apply nth_error_nth';exact Index. }
 assert (RBytesI:schnorr_bytes_at mi bsig osig (schnorr_word_bytes r)).
 { eapply schnorr_bytes_framed;[exact BlockFrame| | |exact RBytes].
   - eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact RBytes].
   - intros;clear -SigSep;cbn [In] in *;intuition congruence. }
 assert (MsgBytesI:schnorr_bytes_at mi bmsg omsg (schnorr_word_bytes msg)).
 { eapply schnorr_bytes_framed;[exact BlockFrame| | |exact MsgBytes].
   - eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact MsgBytes].
   - intros;clear -MsgSep;cbn [In] in *;intuition congruence. }
 assert (StartupI:secp_sha_startup mi).
 { eapply secp_sha_startup_preserved;[exact Startup|exact ReadI|exact BlockFrame|].
   pose proof (proj1 (secp_sha_startup_separate m bbuf 32 Startup ltac:(clear;lia)
    (Owned bbuf 32 ltac:(clear;cbn [In];tauto)))) as Buffer.
   pose proof (proj1 (secp_sha_startup_separate m bpk 88 Startup ltac:(clear;lia)
    (Owned bpk 88 ltac:(clear;cbn [In];tauto)))) as Key.
   intros;split;congruence. }
 assert (TablesI:forall h,generator_table_state h mi).
 { eapply generator_tables_readonly;[exact Tables|exact ReadI]. }
 assert (SplitI:split_constants_ready mi).
 { eapply split_constants_readonly;[exact Split|exact ReadI]. }
 assert (BetaI:beta_initialized mi).
 { eapply beta_initialized_preserved;[exact Beta|exact ReadI]. }
 assert (ReadyI:modinfo_fe_state mi).
 { eapply modinfo_fe_state_unchanged;[exact Ready|].
   eapply Mem.unchanged_on_implies;[exact (proj2 ReadI)|].
   intros b pos Same _;subst b;split;[exact (proj1 (proj1 Ready))|exact (proj2 Ready pos)]. }
 assert (Outside:forall b,In b [bp;bk;ba;bng;br;bx] ->b<>bbuf /\b<>bpk).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (InputNGI:scalar_at mi bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact BlockFrame|];intros;apply Outside;cbn [In];tauto. }
 assert (YI:fe_at mi bpk 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact FrameI|];intros pos Pos Foot.
   destruct (get_b32_foot_bounds bbuf 0 bpk 0 bpk pos Foot) as [[Same _]|[_ Bad]];
    [congruence|change (40<=pos<80) in Pos;lia]. }
 assert (KeyFlagI:Mem.load Mint32 mi bpk 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameI Mint32 bpk 80).
   - exact KeyFlag.
   - eapply Mem.perm_valid_block;apply (Owned bpk 88 ltac:(clear;cbn [In];tauto) 0);lia.
   - intros pos Pos Foot;destruct (get_b32_foot_bounds bbuf 0 bpk 0 bpk pos Foot) as [[Same _]|[_ Bad]];
     [congruence|change (80<=pos<84) in Pos;lia]. }
 assert (RVI:fe_at mi bx 0 (words5 rv)).
 { eapply field_at_lframe;[exact RV|exact BlockFrame|];intros;apply Outside;cbn [In];tauto. }
 assert (OwnedI:forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot pos Pos;apply Keep;exact (Owned b hi ltac:(clear -Slot;cbn [In] in Slot|-*;tauto) pos Pos). }
 assert (SevenSeparate:NoDup [bp;bk;ba;bng;br;bx;bpk]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat constructor;cbn [In] in *;intuition congruence. }
 assert (BX:square_input_bounds (limb_rho value)).
 { intros i Index;pose proof (limb_rho_bound value Range i) as Bound;
   destruct (Nat.eqb i 4);change (0<=Int64.unsigned (limb_rho value i)<=4503599627370495) in Bound;lia. }
 assert (TX:table_word_literal (limb_rho value) ax).
 { destruct (secp_even_decompress_properties pk ax ay Decode) as [AX _].
   unfold table_word_literal;rewrite radix_limb_rho by exact Range.
   rewrite AX,canonical_fe_normalize_numeric,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 change (fe_at mi bpk 0 (words5 (limb_rho value))) in XI.
 destruct (exec_schnorr_challenge_return_canonical Copy Clear Count e le mi bp bk ba bng br bx bpk
  (limb_rho value) y rv ng ax ay r pk msg bsig osig bmsg omsg bbuf
  Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound RBytesI KeyBytes MsgBytesI StartupI
  NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES SevenSeparate OwnedI TablesI SplitI BetaI ReadyI
  InputNGI BX BY BR XI YI KeyFlagI RVI TX TY TR PKBound RBound SBound Decode)
 as (mf & lef & Rest & OwnedF & FrameF & ForwardF).
 assert (Call:Clight2.exec_stmt secp_ge e le m schnorr_serialize_call E0 le mi Out_normal).
 { unfold schnorr_serialize_call;eapply exec_curve_call with
    (vargs:=[Vptr bbuf Ptrofs.zero;Vptr bpk Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact SerializeSym.
   - eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|].
     eapply eval_Econs;[apply eval_schnorr_key_x_address;exact PK|reflexivity|constructor].
   - exact Serialize. }
 exists mf,lef;split.
 - unfold schnorr_serialize_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le);[exact Call|exact Rest].
 - split.
   + intros b hi Slot;destruct (Pos.eq_dec b bbuf) as [Same|Other].
     { subst b;assert (Size:hi=32) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi.
       eapply curve_keep_free;[lia| |exact FrameF|].
       - intros pos Pos;apply Keep;exact (Owned bbuf 32 ltac:(clear;cbn [In];tauto) pos Pos).
       - intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
     apply OwnedF;clear -Slot Other;cbn [In] in *;intuition congruence.
   + split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact BlockFrame|];intros b pos Out _;clear -Out;cbn [In] in *;intuition congruence. }
       { eapply lframe_implies;[exact FrameF|];intros b pos Out _;clear -Out;cbn [In] in *;tauto. }
     * eapply mem_forward_trans;[exact (proj1 ReadI)|exact ForwardF].
Qed.
