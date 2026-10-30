(** Original Schnorr multiplier call composed with conversion and return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_clight_forward
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_rescale_literal C.jet_secp_odd_table_literal_walk
 C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_generator_globals C.jet_secp_split_constants C.jet_secp_beta_global
 C.jet_secp_ecmult_general C.jet_secp_table_affine_nonzero C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_strauss_complete_program C.jet_secp_literal_gej_predicate
 C.jet_secp_even_x_test C.jet_secp_modinfo_fe_caller C.jet_ctz_model C.jet_memset_model
 C.jet_secp_root_chain_owned C.jet_secp_schnorr_after_mult
 C.jet_secp_scalar_table_literal C.jet_secp_canonical_zero C.jet_secp_strauss_complete_program
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Require Import C.jet_secp_modinfo_fe_transport.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_off_curve_linear_combination_1 literal_gej_is_infinity
 rescale_field_output literal_scalar_table5 canonical_fe_is_zero.
Definition schnorr_mult_call:=curve_call _secp256k1_ecmult f_secp256k1_ecmult None
 [Eaddrof (Evar _rj (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _pkj (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _e (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr))].
Definition schnorr_mult_return:=Ssequence schnorr_mult_call schnorr_after_mult_tail.
Lemma schnorr_mult_return_source:
 root_drop_statements 11 (fn_body f_secp256k1_schnorrsig_verify)=schnorr_mult_return.
Proof. reflexivity. Qed.
Theorem exec_schnorr_mult_return_owned (Clear:memset_model) (Count:ctz_model)
 e le m bp bk ba bng br bx x y z rv (raw ng ax ay r:Ty.tySem (Word 8)):
 e!_rj=Some (bp,Tstruct __6123 noattr) ->e!_pkj=Some (ba,Tstruct __6123 noattr) ->
 e!_e=Some (bk,Tstruct __5826 noattr) ->e!_s=Some (bng,Tstruct __5826 noattr) ->
 e!_r=Some (br,curve_ge_type) ->e!_rx=Some (bx,curve_fe_type) ->
 e!_secp256k1_ecmult=None ->e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_ge_is_infinity=None ->
 e!_secp256k1_fe_normalize_var=None ->e!_secp256k1_fe_is_odd=None ->e!_secp256k1_fe_equal_var=None ->
 NoDup [bp;bk;ba;bng;br;bx] ->
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40)] ->
  Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem raw)))) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
 (forall i,(i<5)%nat ->Int64.unsigned (rv i)<if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
 fe_at m ba 0 (words5 x) ->fe_at m ba 40 (words5 y) ->fe_at m ba 80 (words5 z) ->fe_at m bx 0 (words5 rv) ->
 table_word_literal x ax ->table_word_literal y ay ->
 table_word_literal z (@literal_fe_one256 Simplicity.Alg.CoreFunSem tt) ->
 radix_value rv mod feP=@toZ (WordToZ 8) r ->
 Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem
   ((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt))))) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m schnorr_mult_return E0 lef mf
  (Out_return (Some (Vint (bit_int (secp_even_x_test
   (@literal_off_curve_linear_combination_1 Simplicity.Alg.CoreFunSem
    ((raw,((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)),ng)) r)),tint))) /\
 (forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32);(br,88);(bx,40)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun block _=>~In block [bp;bk;ba;bng;br;bx]) m mf /\mem_forward m mf.
Proof.
 intros RJ PKJ E S R RX MS CS IS NS OS ES Separate Owned Tables Split Beta Ready
  Input InputNG BX BY BZ BR X Y Z RV TX TY TZ TR ValidCurve Flag.
 assert (FourSeparate:NoDup [bp;bk;ba;bng]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;repeat constructor;cbn [In] in *;intuition congruence. }
 assert (FourOwned:forall b hi,In (b,hi) [(bp,128);(bk,32);(ba,128);(bng,32)] ->
  Mem.range_perm m b 0 hi Cur Freeable).
 { intros b hi Slot;apply Owned;cbn [In] in Slot|-*;tauto. }
 destruct (eval_ecmult_general_flag_forward Clear raw ng ax ay
  (@literal_fe_one256 Simplicity.Alg.CoreFunSem tt) x y z m bp bk ba bng
  Tables Split Beta FourSeparate FourOwned Input InputNG BX BY BZ X Y Z Flag TX TY TZ)
 as (mm & ox & oy & oz & Mult & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedM & TablesM & FrameM & FlagM & ForwardM).
 assert (ReadyM:modinfo_fe_state mm).
 { eapply modinfo_fe_state_owned_frame with (slots:=[(bp,128);(bk,32);(ba,128);(bng,32)]);
   [exact Ready|exact ForwardM| |exact FrameM].
   intros b hi Slot;split;[clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia|apply FourOwned;exact Slot]. }
 assert (Outside:forall b,In b [br;bx] ->~In b [bp;bk;ba;bng]).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (RVM:fe_at mm bx 0 (words5 rv)).
 { eapply field_at_lframe;[exact RV|exact FrameM|];intros;apply Outside;cbn [In];tauto. }
 assert (FRM:Mem.range_perm mm br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|apply Owned;cbn [In];tauto|exact FrameM|];intros;apply Outside;cbn [In];tauto. }
 assert (FXM:Mem.range_perm mm bx 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|apply Owned;cbn [In];tauto|exact FrameM|];intros;apply Outside;cbn [In];tauto. }
 assert (OutputFlag:Mem.load Mint32 mm bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem
   ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)))))).
 { rewrite literal_gej_is_infinity_value;apply FlagM;apply literal_affine_scalar_table_nonzero;exact ValidCurve. }
 assert (Pairwise:bp<>br /\bp<>bx /\br<>bx).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct Pairwise as [PR [PX RXSep]].
 destruct (exec_schnorr_after_mult_owned Count e le mm bp br bx ox oy oz rv
  (rescale_field_output ox) (rescale_field_output oy) (rescale_field_output oz) r
  R RJ RX CS IS NS OS ES PR PX RXSep BXO BYO BZO BR XO YO ZO RVM
  (table_decoded_literal ox _ eq_refl) (table_decoded_literal oy _ eq_refl)
  (table_decoded_literal oz _ eq_refl) TR OutputFlag ReadyM
  (OwnedM bp 128 ltac:(cbn [In];tauto)) FRM FXM)
 as (mf & lef & Tail & FPF & FRF & FXF & FrameF & ReadF).
 assert (Call:Clight2.exec_stmt secp_ge e le m schnorr_mult_call E0 le mm Out_normal).
 { unfold schnorr_mult_call;eapply exec_curve_call with
    (vargs:=[Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bk Ptrofs.zero;Vptr bng Ptrofs.zero]) (v:=Vundef).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact MS.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact RJ|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact PKJ|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact E|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact S|reflexivity|constructor].
   - exact Mult. }
 exists mf,lef;split.
 - rewrite <-Literal;unfold schnorr_mult_return;eapply exec_Sseq_1 with
    (t1:=E0) (t2:=E0) (m1:=mm) (le1:=le);[exact Call|exact Tail].
 - split.
   + intros b hi Slot;destruct (Pos.eq_dec b bp) as [Same|OtherP].
     { subst b;assert (Size:hi=128) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FPF. }
     destruct (Pos.eq_dec b br) as [Same|OtherR].
     { subst b;assert (Size:hi=88) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FRF. }
     destruct (Pos.eq_dec b bx) as [Same|OtherX].
     { subst b;assert (Size:hi=40) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence);subst hi;exact FXF. }
     eapply curve_keep_free;[clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia| |exact FrameF|intros;repeat split;assumption].
     apply OwnedM;clear -Slot OtherR OtherX;cbn [In] in Slot|-*;intuition congruence.
   + split.
     * eapply lframe_trans.
       { eapply lframe_implies;[exact FrameM|];intros block pos OutsideAll _;clear -OutsideAll;cbn [In] in *;tauto. }
       { eapply lframe_implies;[exact FrameF|];intros block pos OutsideAll _;clear -OutsideAll;cbn [In] in *;intuition congruence. }
     * eapply mem_forward_trans;[exact ForwardM|exact (proj1 ReadF)].
Qed.
