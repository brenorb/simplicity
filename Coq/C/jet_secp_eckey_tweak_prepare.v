(** Original key/one initialization and actual in-place tweak multiplication. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_eckey_tweak_entry C.jet_secp_gej_set_ge_owned C.jet_secp_scalar_set_int_owned
 C.jet_secp_scalar_add_reader_support C.jet_secp_ecmult_overlap_finite C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_canonical_scalar C.jet_secp_point_set_bit C.jet_secp_generator_preprocess
 C.jet_secp_generator_pair_general C.jet_secp_generator_main C.jet_secp_generator_globals C.jet_secp_split_constants C.jet_secp_beta_global C.jet_secp_beta_state
 C.jet_secp_modinfo_fe_caller C.jet_secp_modinfo_fe_transport C.jet_secp_table_affine_nonzero
 C.jet_secp_curve_literal C.jet_secp_scalar_table_literal C.jet_secp_literal_add_numeric C.jet_secp_literal_add_program
 C.jet_secp_strauss_complete_program C.jet_secp_literal_gej_predicate C.jet_secp_canonical_zero
 C.jet_secp_odd_table_literal_walk C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_rescale_literal C.jet_secp_field_zero_owned C.jet_secp_closed_helpers
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_readBit_layout C.jet_sx_mem
 C.jet_memset_model C.jet_clight_forward C.jet_clight_internal_preserve C.jet_word_repr.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition eckey_scalar_one:Ty.tySem (Word 8):=@fromZ (WordToZ 8) 1.
Lemma eckey_scalar_one_value:@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem eckey_scalar_one)=1.
Proof. vm_compute;reflexivity. Qed.
Lemma eckey_scalar_one_limbs:
 map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem eckey_scalar_one)))=
 [Int64.one;Int64.zero;Int64.zero;Int64.zero].
Proof. rewrite eckey_scalar_one_value;reflexivity. Qed.
Definition eckey_tweak_prepare:=Ssequence eckey_tweak_set_ge (Ssequence eckey_tweak_set_one eckey_tweak_mult).
Definition eckey_tweak_point (ng ax ay:Ty.tySem (Word 8)):=
 @literal_strauss_body Simplicity.Alg.CoreFunSem ((eckey_scalar_one,((ax,ay),@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)),ng).
Local Opaque secp_ge literal_strauss_body rescale_field_output literal_scalar_table5 canonical_fe_is_zero.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_eckey_tweak_prepare (Model:memset_model) (ng ax ay:Ty.tySem (Word 8)) x y le m bp bo bk bt:
 le!_key=Some (Vptr bk Ptrofs.zero) ->le!_tweak=Some (Vptr bt Ptrofs.zero) ->
 NoDup [bp;bo;bk;bt] ->
 (forall b hi,In (b,hi) [(bp,128);(bo,32);(bk,88);(bt,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 scalar_at m bt 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds x ->square_input_bounds y ->fe_at m bk 0 (words5 x) ->fe_at m bk 40 (words5 y) ->Mem.load Mint32 m bk 80=Some (Vint Int.zero) ->
 table_word_literal x ax ->table_word_literal y ay ->Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->exists mf ox oy oz,
 Clight2.exec_stmt secp_ge (eckey_tweak_env bp bo) le m eckey_tweak_prepare E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 ox) /\fe_at mf bp 40 (words5 oy) /\fe_at mf bp 80 (words5 oz) /\
 square_input_bounds ox /\square_input_bounds oy /\square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=eckey_tweak_point ng ax ay /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz))))) /\
 (forall b hi,In (b,hi) [(bp,128);(bo,32);(bk,88);(bt,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 modinfo_fe_state mf /\lframe (fun b _=>b<>bp /\b<>bo /\b<>bt) m mf /\mem_forward m mf.
Proof.
 intros Key Tweak Separate Owned Tables Split Beta Ready InputNG BX BY X Y KeyFlag TX TY Curve.
 destruct (eval_gej_set_ge_owned m bp bk x y Int.zero ltac:(distinct Separate)
  (Owned bp 128 ltac:(clear;cbn [In];tauto)) X Y KeyFlag)
 as (mj & InitPoint & XJ & YJ & ZJ & FlagJ & FPJ & FrameJ).
 assert (ReadJ:readonly_preserved m mj).
 { eapply secp_closed_function_preserved with (fd:=f_secp256k1_gej_set_ge);
   [vm_compute;reflexivity|reflexivity|exact InitPoint]. }
 assert (FOJ:Mem.range_perm mj bo 0 32 Cur Freeable).
 { eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameJ|intros;distinct Separate]. }
 destruct (eval_scalar_set_int_owned Int.one mj bo FOJ)
 as (ms & InitOne & One & FOS & FrameO & ReadO).
 assert (FrameS:lframe (fun b _=>b<>bp /\b<>bo) m ms).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameJ|intros b pos [P O] Old;exact P].
   - eapply lframe_implies;[exact FrameO|intros b pos [P O] Old;exact O]. }
 assert (ReadS:readonly_preserved m ms) by (eapply preserved_trans;[exact ReadJ|exact ReadO]).
 assert (TablesS:forall h,generator_table_state h ms) by (eapply generator_tables_readonly;[exact Tables|exact ReadS]).
 assert (SplitS:split_constants_ready ms) by (eapply split_constants_readonly;[exact Split|exact ReadS]).
 assert (BetaS:beta_initialized ms) by (eapply beta_initialized_preserved;[exact Beta|exact ReadS]).
 assert (XPS:fe_at ms bp 0 (words5 x)) by (eapply field_at_lframe;[exact XJ|exact FrameO|intros;distinct Separate]).
 assert (YPS:fe_at ms bp 40 (words5 y)) by (eapply field_at_lframe;[exact YJ|exact FrameO|intros;distinct Separate]).
 change (fe_at mj bp 80 (words5 (point_set_bit_words true))) in ZJ.
 assert (ZPS:fe_at ms bp 80 (words5 (point_set_bit_words true))) by (eapply field_at_lframe;[exact ZJ|exact FrameO|intros;distinct Separate]).
 assert (FlagS:Mem.load Mint32 ms bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameO);[exact FlagJ|eapply Mem.perm_valid_block;apply (FPJ 0);lia|intros;distinct Separate]. }
 assert (FPS:Mem.range_perm ms bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FPJ|exact FrameO|intros;distinct Separate]. }
 assert (FTS:Mem.range_perm ms bt 0 32 Cur Freeable).
 { eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameS|intros;split;distinct Separate]. }
 assert (InputS:scalar_at ms bt 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameS|intros;split;distinct Separate]. }
 assert (OneS:scalar_at ms bo 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8)
  (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem eckey_scalar_one))))).
 { rewrite eckey_scalar_one_limbs;exact One. }
 assert (OneLiteral:table_word_literal (point_set_bit_words true) (@literal_fe_one256 Simplicity.Alg.CoreFunSem tt)).
 { unfold table_word_literal;rewrite generator_denominator_one_value,literal_fe_one256_value;reflexivity. }
 destruct (eval_ecmult_overlap_finite_flag_forward Model eckey_scalar_one ng ax ay
  (@literal_fe_one256 Simplicity.Alg.CoreFunSem tt) x y (point_set_bit_words true) ms bp bo bp bt
  TablesS SplitS BetaS
  ltac:(repeat constructor;cbn [In];distinct Separate)
  ltac:(repeat constructor;cbn [In];distinct Separate)
  ltac:(intros b hi [Slot|[Slot|[Slot|[Slot|Empty]]]];try contradiction;inversion Slot;subst;assumption)
  OneS InputS ltac:(rewrite eckey_scalar_one_value;lia) ltac:(vm_compute;reflexivity)
  BX BY generator_denominator_one_bounds XPS YPS ZPS FlagS TX TY OneLiteral)
 as (mf & ox & oy & oz & Mult & XO & YO & ZO & BXO & BYO & BZO & Literal & OwnedM & TablesM & FrameM & Conditional & ForwardM).
 assert (FlagF:Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)))))).
 { rewrite literal_gej_is_infinity_value;apply Conditional;apply literal_affine_scalar_table_nonzero;exact Curve. }
 assert (Frame:lframe (fun b _=>b<>bp /\b<>bo /\b<>bt) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameS|intros b pos [P [O T]] Old;split;assumption].
   - eapply lframe_implies;[exact FrameM|intros b pos [P [O T]] Old;cbn [In];intuition congruence]. }
 assert (Forward:mem_forward m mf) by (eapply mem_forward_trans;[exact (proj1 ReadS)|exact ForwardM]).
 assert (OwnedF:forall b hi,In (b,hi) [(bp,128);(bo,32);(bk,88);(bt,32)] ->Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi [Slot|[Slot|[Slot|[Slot|Empty]]]];try contradiction;inversion Slot;subst.
   - apply OwnedM;clear;cbn [In];tauto.
   - apply OwnedM;clear;cbn [In];tauto.
   - eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact Frame|intros;repeat split;distinct Separate].
   - apply OwnedM;clear;cbn [In];tauto. }
 exists mf,ox,oy,oz;split.
 - unfold eckey_tweak_prepare;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mj) (le1:=le).
   + unfold eckey_tweak_set_ge;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * reflexivity.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact Key|reflexivity|constructor].
     * exact InitPoint.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
     * unfold eckey_tweak_set_one;eapply exec_curve_call with (vargs:=[Vptr bo Ptrofs.zero;Vint Int.one]) (v:=Vundef).
       -- unfold secp_pure;repeat first [left;reflexivity|right].
       -- reflexivity.
       -- eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
          eapply eval_Econs;[constructor|reflexivity|constructor].
       -- exact InitOne.
     * unfold eckey_tweak_mult;eapply exec_curve_call with
       (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bo Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
       -- unfold secp_pure;repeat first [left;reflexivity|right].
       -- reflexivity.
       -- do 3 (eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|]).
          eapply eval_Econs;[apply eval_Etempvar;exact Tweak|reflexivity|constructor].
       -- exact Mult.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];
   split;[exact Literal|];split;[exact FlagF|];split;[exact OwnedF|];split.
   + eapply modinfo_fe_state_owned_frame with (slots:=[(bp,128);(bo,32);(bt,32)]);
     [exact Ready|exact Forward| |].
     * intros b hi [Slot|[Slot|[Slot|Empty]]];try contradiction;inversion Slot;subst;split;try lia;apply Owned;clear;cbn [In];tauto.
     * eapply lframe_implies;[exact Frame|];intros b pos Outside Old;cbn [map fst In] in Outside;repeat split;intuition congruence.
   + split;[exact Frame|exact Forward].
Qed.
