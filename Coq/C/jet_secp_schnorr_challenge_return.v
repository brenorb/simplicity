(** Original Schnorr challenge, scalar negation and arithmetic return. *)
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
Definition schnorr_challenge_call:=curve_call _secp256k1_schnorrsig_challenge f_secp256k1_schnorrsig_challenge None
 [Eaddrof (Evar _e (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Ebinop Cop.Oadd (Etempvar _sig64 (tptr tuchar)) (Econst_int Int.zero tint) (tptr tuchar);
  Etempvar _msg (tptr tuchar);Etempvar _msglen tulong;Evar _buf (tarray tuchar 32)].
Definition schnorr_challenge_return:=Ssequence schnorr_challenge_call schnorr_negate_return.
Lemma schnorr_challenge_return_source:
 root_drop_statements 8 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_challenge_return.
Proof. reflexivity. Qed.
Theorem exec_schnorr_challenge_return_owned (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
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
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_challenge_return E0 lef mf
  (Out_return (Some (Vint (bit_int (secp_even_x_test
   (@literal_off_curve_linear_combination_1 Simplicity.Alg.CoreFunSem
    ((@canonical_scalar_negate Simplicity.Alg.CoreFunSem
     (@literal_bip0340_challenge Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))),((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)),ng)) r)),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk]) m mf /\mem_forward m mf.
Proof.
 intros Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound RBytes PKBytes MsgBytes Startup
  NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate Owned Tables Split Beta Ready
  InputNG BX BY BR X Y KeyFlag RV TX TY TR ValidCurve.
 destruct (eval_schnorr_challenge_literal Copy pk msg r ng m bk bsig osig bmsg omsg bbuf Ptrofs.zero
  Startup (Owned bk 32 ltac:(cbn [In];tauto)) SigBound
  ltac:(change (32<=18446744073709551615);lia) MsgBound RBytes PKBytes MsgBytes)
 as (mi & Challenge & InputI & FreeK & FrameI & ReadI & StartupI).
 assert (TablesI:forall h,generator_table_state h mi).
 { eapply generator_tables_readonly;[exact Tables|exact ReadI]. }
 assert (SplitI:split_constants_ready mi).
 { eapply split_constants_readonly;[exact Split|exact ReadI]. }
 assert (BetaI:beta_initialized mi).
 { eapply beta_initialized_preserved;[exact Beta|exact ReadI]. }
 assert (ReadyI:modinfo_fe_state mi).
 { eapply modinfo_fe_state_owned_frame with (slots:=[(bk,32)]);
   [exact Ready|exact (proj1 ReadI)| |].
   - intros b hi [Slot|[]];inversion Slot;subst;split;[lia|apply Owned;cbn [In];tauto].
   - eapply lframe_implies;[exact FrameI|];intros b pos Outside _;clear -Outside;cbn [map fst In] in *;intuition congruence. }
 assert (InputNormalized:scalar_at mi bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem
   (@literal_bip0340_challenge Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng)))))))).
 { rewrite literal_bip0340_challenge_value in *.
   rewrite secp_scalar_normalize_idempotent;exact InputI. }
 assert (InputNGI:scalar_at mi bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameI|];intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (XI:fe_at mi bpk 0 (words5 x)).
 { eapply field_at_lframe;[exact X|exact FrameI|];intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (YI:fe_at mi bpk 40 (words5 y)).
 { eapply field_at_lframe;[exact Y|exact FrameI|];intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (RVI:fe_at mi bx 0 (words5 rv)).
 { eapply field_at_lframe;[exact RV|exact FrameI|];intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (KeyFlagI:Mem.load Mint32 mi bpk 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameI Mint32 bpk 80);[exact KeyFlag| |].
   - eapply Mem.perm_valid_block;apply (Owned bpk 88 ltac:(cbn [In];tauto) 0);lia.
   - intros;clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (OwnedI:forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (Pos.eq_dec b bk) as [Same|Other].
   - subst b;assert (Size:hi=32) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FreeK.
   - eapply curve_keep_free;[ |apply Owned;exact Slot|exact FrameI|intros;exact Other].
     clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia. }
 destruct (exec_schnorr_negate_return_owned Clear Count e le mi bp bk ba bng br bx bpk x y rv
  (@literal_bip0340_challenge Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))) ng ax ay r
  NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate OwnedI TablesI SplitI BetaI ReadyI
  InputNormalized InputNGI BX BY BR XI YI KeyFlagI RVI TX TY TR ValidCurve)
 as (mf & lef & Rest & OwnedF & FrameF & ForwardF).
 assert (Call:Clight2.exec_stmt secp_ge e le m schnorr_challenge_call E0 le mi Out_normal).
 { unfold schnorr_challenge_call;eapply exec_curve_call with
    (vargs:=[Vptr bk Ptrofs.zero;Vptr bsig osig;Vptr bmsg omsg;Vlong (Int64.repr 32);Vptr bbuf Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact ChallengeSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact E|reflexivity|].
     eapply eval_Econs with (v1:=Vptr bsig osig).
     { eapply eval_Ebinop;[apply eval_Etempvar;exact Sig|constructor|].
       change (Some (Vptr bsig (Ptrofs.add osig Ptrofs.zero))=Some (Vptr bsig osig)).
       rewrite Ptrofs.add_zero;reflexivity. }
     { reflexivity. }
     eapply eval_Econs;[apply eval_Etempvar;exact Msg|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact MsgLen|reflexivity|].
     eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|constructor].
   - exact Challenge. }
 exists mf,lef;split.
 - unfold schnorr_challenge_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le);[exact Call|exact Rest].
 - split;[exact OwnedF|];split.
   + eapply lframe_trans.
     { eapply lframe_implies;[exact FrameI|];intros b pos Outside _;clear -Outside;cbn [In] in *;intuition congruence. }
     { exact FrameF. }
   + eapply mem_forward_trans;[exact (proj1 ReadI)|exact ForwardF].
Qed.
