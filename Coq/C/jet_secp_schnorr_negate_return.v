(** Original Schnorr scalar negation through the final return. *)
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
Definition schnorr_negate_call:=curve_call _secp256k1_scalar_negate f_secp256k1_scalar_negate None
 [Eaddrof (Evar _e (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _e (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition schnorr_negate_return:=Ssequence schnorr_negate_call schnorr_gej_mult_return.
Lemma schnorr_negate_return_source:
 root_drop_statements 9 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_negate_return.
Proof. reflexivity. Qed.
Lemma schnorr_negate_closed:
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_negate)=true.
Proof. vm_compute;reflexivity. Qed.
Theorem exec_schnorr_negate_return_owned (Clear:memset_model) (Count:ctz_model)
 e le m bp bk ba bng br bx bpk x y rv (raw ng ax ay r:Ty.tySem (Word 8)):
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
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds x ->square_input_bounds y ->
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m bpk 0 (words5 x) ->fe_at m bpk 40 (words5 y) ->Mem.load Mint32 m bpk 80=Some (Vint Int.zero) ->fe_at m bx 0 (words5 rv) ->
 table_word_literal x ax ->table_word_literal y ay ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_negate_return E0 lef mf
  (Out_return (Some (Vint (bit_int (secp_even_x_test
   (@literal_off_curve_linear_combination_1 Simplicity.Alg.CoreFunSem
    ((@canonical_scalar_negate Simplicity.Alg.CoreFunSem raw,((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)),ng)) r)),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40);(bpk,88)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx;bpk]) m mf /\mem_forward m mf.
Proof.
 intros NegSym PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate Owned Tables Split Beta Ready
  Input InputNG BX BY BR X Y KeyFlag RV TX TY TR ValidCurve.
 pose (value:=@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem raw)).
 pose proof (scalar_writer_initial_rep_from_storage value m bk Input
  (Owned bk 32 ltac:(cbn [In];tauto))) as NegRep.
 destruct (eval_scalar_negate_canonical_owned _ [(bk,0)] m raw NegRep
  (scalar_limb_rho_value value (word_toZ_range 8 (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem raw))))
 as (mi & Neg & NegStorage & NegWriter & FreeK & NegFrame).
 cbn [blk bas lay nth fst snd] in Neg,NegStorage,FreeK.
 assert (FrameI:lframe (fun b _=>b<>bk) m mi).
 { eapply lframe_implies;[exact NegFrame|];intros b pos Other _ Foot.
   apply Other;exact (scalar_writer_foot_block bk b pos Foot). }
 assert (ReadI:readonly_preserved m mi).
 { eapply secp_closed_function_preserved;[exact schnorr_negate_closed|reflexivity|exact Neg]. }
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
 assert (InputI:scalar_at mi bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem
   (@canonical_scalar_negate Simplicity.Alg.CoreFunSem raw)))))).
 { rewrite scalar_negate_normalize_identity;exact NegStorage. }
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
 destruct (exec_schnorr_gej_mult_return_owned Clear Count e le mi bp bk ba bng br bx bpk x y rv
  (@canonical_scalar_negate Simplicity.Alg.CoreFunSem raw) ng ax ay r
  PK JS RJ PKJ E S R RX MS CS IS NS OS ES Separate OwnedI TablesI SplitI BetaI ReadyI
  InputI InputNGI BX BY BR XI YI KeyFlagI RVI TX TY TR ValidCurve)
 as (mf & lef & Rest & OwnedF & FrameF & ForwardF).
 assert (Call:Clight2.exec_stmt secp_ge e le m schnorr_negate_call E0 le mi Out_normal).
 { unfold schnorr_negate_call;eapply exec_curve_call with
    (vargs:=[Vptr bk Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact NegSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact E|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact E|reflexivity|constructor].
   - exact Neg. }
 exists mf,lef;split.
 - unfold schnorr_negate_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le);[exact Call|exact Rest].
 - split;[exact OwnedF|];split.
   + eapply lframe_trans.
     { eapply lframe_implies;[exact FrameI|];intros b pos Outside _;clear -Outside;cbn [In] in *;intuition congruence. }
     { exact FrameF. }
   + eapply mem_forward_trans;[exact (proj1 ReadI)|exact ForwardF].
Qed.
