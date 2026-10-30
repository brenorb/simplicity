(** Original opaque-key load and guard through the canonical Schnorr return. *)
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
Definition schnorr_keyload_call:=curve_call _secp256k1_xonly_pubkey_load f_secp256k1_xonly_pubkey_load (Some _t'3)
 [Eaddrof (Evar _pk curve_ge_type) (tptr curve_ge_type);
  Etempvar _pubkey (tptr (Tstruct __6478 noattr))].
Definition schnorr_keyload_guard:=Ssequence schnorr_keyload_call
 (Sifthenelse (Eunop Cop.Onotbool (Etempvar _t'3 tint) tint)
  (Sreturn (Some (Econst_int Int.zero tint))) Sskip).
Definition schnorr_keyload_return:=Ssequence schnorr_keyload_guard schnorr_serialize_return.
Lemma schnorr_keyload_return_source:
 root_drop_statements 6 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_keyload_return.
Proof. reflexivity. Qed.
Theorem exec_schnorr_keyload_return_canonical (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 w e le m bp bk ba bng br bx bpk rv (ng ax ay r pk msg:Ty.tySem (Word 8))
 bsig osig bmsg omsg bbuf bkey keybase:
 e!_secp256k1_xonly_pubkey_load=None ->
 le!_pubkey=Some (Vptr bkey (Ptrofs.repr keybase)) ->
 affine_storage_readable m bkey keybase w ->
 field_storage_value w=@toZ (WordToZ 8) pk ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
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
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m bx 0 (words5 rv) ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 @toZ (WordToZ 8) pk<feP ->@toZ (WordToZ 8) r<feP ->@toZ (WordToZ 8) ng<canonical_group_order ->
 @literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_keyload_return E0 lef mf
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,ng))))),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk;bbuf]) m mf /\mem_forward m mf.
Proof.
 intros LoadSym KeyPtr KeyInput KeyX KeyY SerializeSym Buf ChallengeSym Sig Msg MsgLen SigBound MsgBound
  RBytes MsgBytes Startup NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES
  Separate SigSep MsgSep Owned Tables Split Beta Ready InputNG BR RV TR PKBound RBound SBound Decode.
 pose proof (secp_decompress_curve pk (inl tt) (ax,ay) Decode) as Curve.
 destruct (secp_even_decompress_properties pk ax ay Decode) as (AX & _).
 assert (AXValue:@toZ (WordToZ 8) ax=@toZ (WordToZ 8) pk).
 { rewrite AX,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model;apply Z.mod_small.
   split;[exact (proj1 (word_toZ_range 8 pk))|exact PKBound]. }
 assert (StoredX:field_storage_value w=@toZ (WordToZ 8) ax) by (rewrite AXValue;exact KeyX).
 destruct (eval_xonly_pubkey_load_coordinates Copy w m bkey keybase bpk ax ay
  (Owned bpk 88 ltac:(clear;cbn [In];tauto)) KeyInput StoredX KeyY Curve)
 as (mi & Load & XI & YI & KeyFlag & FreeKey & FrameI & ReadI).
 rewrite AXValue in XI.
 pose (li:=PTree.set _t'3 (Vint Int.one) le).
 assert (SigI:li!_sig64=Some (Vptr bsig osig)) by (unfold li;rewrite PTree.gso by discriminate;exact Sig).
 assert (MsgI:li!_msg=Some (Vptr bmsg omsg)) by (unfold li;rewrite PTree.gso by discriminate;exact Msg).
 assert (MsgLenI:li!_msglen=Some (Vlong (Int64.repr 32))) by (unfold li;rewrite PTree.gso by discriminate;exact MsgLen).
 assert (RBytesI:schnorr_bytes_at mi bsig osig (schnorr_word_bytes r)).
 { eapply schnorr_bytes_framed;[exact FrameI| | |exact RBytes].
   - eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact RBytes].
   - intros;clear -SigSep;cbn [In] in *;intuition congruence. }
 assert (MsgBytesI:schnorr_bytes_at mi bmsg omsg (schnorr_word_bytes msg)).
 { eapply schnorr_bytes_framed;[exact FrameI| | |exact MsgBytes].
   - eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact MsgBytes].
   - intros;clear -MsgSep;cbn [In] in *;intuition congruence. }
 assert (StartupI:secp_sha_startup mi).
 { eapply secp_sha_startup_preserved;[exact Startup|exact ReadI|exact FrameI|].
   pose proof (proj1 (secp_sha_startup_separate m bpk 88 Startup ltac:(clear;lia)
    (Owned bpk 88 ltac:(clear;cbn [In];tauto)))) as Key.
   intros;congruence. }
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
 assert (Outside:forall b,In b [bp;bk;ba;bng;br;bx;bbuf] ->b<>bpk).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (InputNGI:scalar_at mi bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameI|];intros;apply Outside;cbn [In];tauto. }
 assert (RVI:fe_at mi bx 0 (words5 rv)).
 { eapply field_at_lframe;[exact RV|exact FrameI|];intros;apply Outside;cbn [In];tauto. }
 assert (OwnedI:forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88);(bbuf,32)] ->
  Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (Pos.eq_dec b bpk) as [Same|Other].
   - subst b;assert (Size:hi=88) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FreeKey.
   - eapply curve_keep_free;[ |apply Owned;exact Slot|exact FrameI|intros;exact Other].
     clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia. }
 pose (yv:=limb_rho (@toZ (WordToZ 8) ay)).
 assert (BY:square_input_bounds yv).
 { intros i Index;pose proof (limb_rho_bound (@toZ (WordToZ 8) ay) (word_toZ_range 8 ay) i) as Bound.
   unfold yv;destruct (Nat.eqb i 4);change (0<=Int64.unsigned (limb_rho (@toZ (WordToZ 8) ay) i)<=4503599627370495) in Bound;lia. }
 assert (TY:table_word_literal yv ay).
 { unfold table_word_literal,yv;rewrite radix_limb_rho by apply word_toZ_range;reflexivity. }
 change (fe_at mi bpk 40 (words5 yv)) in YI.
 destruct (exec_schnorr_serialize_return_canonical Copy Clear Count e li mi bp bk ba bng br bx bpk yv rv
  ng ax ay r pk msg bsig osig bmsg omsg bbuf SerializeSym Buf ChallengeSym SigI MsgI MsgLenI
  SigBound MsgBound RBytesI MsgBytesI StartupI NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES
  Separate SigSep MsgSep OwnedI TablesI SplitI BetaI ReadyI InputNGI BY BR XI YI KeyFlag RVI TY TR
  PKBound RBound SBound Decode)
 as (mf & lef & Rest & OwnedF & FrameF & ForwardF).
 assert (Call:Clight2.exec_stmt secp_ge e le m schnorr_keyload_call E0 li mi Out_normal).
 { unfold schnorr_keyload_call;eapply exec_curve_call with
    (vargs:=[Vptr bpk Ptrofs.zero;Vptr bkey (Ptrofs.repr keybase)]) (v:=Vint Int.one).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact LoadSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact PK|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact KeyPtr|reflexivity|constructor].
   - exact Load. }
 exists mf,lef;split.
 - unfold schnorr_keyload_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=li);[|exact Rest].
   unfold schnorr_keyload_guard;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=li);[exact Call|].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + eapply eval_Eunop;[apply eval_Etempvar;unfold li;apply PTree.gss|reflexivity].
   + reflexivity.
   + constructor.
 - split;[exact OwnedF|];split.
   + eapply lframe_trans.
     { eapply lframe_implies;[exact FrameI|];intros b pos Out _;clear -Out;cbn [In] in *;intuition congruence. }
     { exact FrameF. }
   + eapply mem_forward_trans;[exact (proj1 ReadI)|exact ForwardF].
Qed.
