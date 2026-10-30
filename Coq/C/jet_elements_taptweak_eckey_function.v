(** Full real linked native public-key tweak, both return branches and local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements
 C.jet_sx_mem C.jet_secp_odd_table_literal_walk C.jet_secp_eckey_tweak_entry C.jet_secp_eckey_tweak_prepare C.jet_secp_eckey_tweak_finish
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
 C.jet_secp_canonical_scalar C.jet_secp_generator_pair_general C.jet_secp_generator_globals
 C.jet_secp_split_constants C.jet_secp_beta_global C.jet_secp_beta_state C.jet_secp_table_affine_nonzero
 C.jet_secp_curve_literal C.jet_secp_scalar_table_literal C.jet_secp_literal_gej_predicate C.jet_secp_gej_norm_literal
 C.jet_secp_modinfo_fe_caller C.jet_secp_modinfo_fe_transport C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_rescale_literal C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve C.jet_frame_inv C.jet_readBit_layout.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition eckey_tweak_infinite ng ax ay:=Simplicity.Bit.toBool
 (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem (eckey_tweak_point ng ax ay)).
Definition eckey_tweak_value ng ax ay:option (Ty.tySem (Ty.Prod (Word 8) (Word 8))):=
 if eckey_tweak_infinite ng ax ay then None else
 Some (@literal_gej_norm Simplicity.Alg.CoreFunSem (eckey_tweak_point ng ax ay)).
Definition eckey_tweak_key_result (value:option (Ty.tySem (Ty.Prod (Word 8) (Word 8)))) m bk:=
 match value with None=>True|Some point=>exists x y,
 fe_at m bk 0 (words5 x) /\fe_at m bk 40 (words5 y) /\square_input_bounds x /\square_input_bounds y /\
 Mem.load Mint32 m bk 80=Some (Vint Int.zero) /\(rescale_field_output x,rescale_field_output y)=point end.
Require Import C.jet_secp_eckey_tweak_function C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_beta.
Require Import C.jet_elements_taptweak_eckey_entry C.jet_elements_taptweak_eckey_prepare C.jet_elements_taptweak_eckey_finish.
Lemma elements_taptweak_eckey_prepare_then_finish e le m li mi lef mf out:
 Clight2.exec_stmt elements_taptweak_ge e le m eckey_tweak_prepare E0 li mi Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e li mi eckey_tweak_finish E0 lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge e le m (fn_body f_secp256k1_eckey_pubkey_tweak_add) E0 lef mf out.
Proof.
 intros Prefix Finish;rewrite eckey_tweak_body_source;unfold eckey_tweak_prepare in Prefix.
 inversion Prefix;subst;try contradiction.
 match goal with H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
 change E0 with (E0**E0);eapply exec_Sseq_1;[eassumption|].
 match goal with H:exec_stmt function_entry2 _ _ _ _ (Ssequence eckey_tweak_set_one eckey_tweak_mult) _ _ _ _ |- _=>
  inversion H;subst;try contradiction end.
 match goal with H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
 change E0 with (E0**E0);eapply exec_Sseq_1;[eassumption|].
 change E0 with (E0**E0);eapply exec_Sseq_1;[eassumption|exact Finish].
Qed.
Local Opaque secp_ge elements_taptweak_ge eckey_tweak_point literal_gej_norm literal_gej_is_infinity rescale_field_output.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem eval_elements_taptweak_eckey_pubkey_tweak_add (Clear:memset_model) (Count:ctz_model)
 (ng ax ay:Ty.tySem (Word 8)) x y m bk bt:
 bk<>bt ->Mem.range_perm m bk 0 88 Cur Freeable ->Mem.range_perm m bt 0 32 Cur Freeable ->
 (forall h,elements_taptweak_generator_table_state h m) ->elements_taptweak_split_ready m ->elements_taptweak_beta_initialized m ->elements_taptweak_modinfo_fe_state m ->
 scalar_at m bt 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng)))) ->
 square_input_bounds x ->square_input_bounds y ->fe_at m bk 0 (words5 x) ->fe_at m bk 40 (words5 y) ->Mem.load Mint32 m bk 80=Some (Vint Int.zero) ->
 table_word_literal x ax ->table_word_literal y ay ->Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_eckey_pubkey_tweak_add)
 [Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mf (Vint (bit_int (negb (eckey_tweak_infinite ng ax ay)))) /\
 eckey_tweak_key_result (eckey_tweak_value ng ax ay) mf bk /\
 Mem.range_perm mf bk 0 88 Cur Freeable /\Mem.range_perm mf bt 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bk /\b<>bt) m mf /\mem_forward m mf /\elements_taptweak_modinfo_fe_state mf /\readonly_preserved m mf.
Proof.
 intros KT FK FT Tables Split Beta Ready InputNG BX BY X Y KeyFlag TX TY Curve.
 assert (VK:Mem.valid_block m bk) by (eapply Mem.perm_valid_block;apply (FK 0);lia).
 assert (VT:Mem.valid_block m bt) by (eapply Mem.perm_valid_block;apply (FT 0);lia).
 destruct (elements_taptweak_eckey_entry m bk bt) as (mi & bp & bo & Entry & PO & Fresh & FPI & FOI & FrameI & KeepI & ReadI).
 assert (Separate:NoDup [bp;bo;bk;bt]).
 { pose proof (Fresh bk VK);pose proof (Fresh bt VT);repeat constructor;cbn [In];intuition congruence. }
 assert (OwnedI:forall b hi,In (b,hi) [(bp,128);(bo,32);(bk,88);(bt,32)] ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi [Slot|[Slot|[Slot|[Slot|Empty]]]];try contradiction;inversion Slot;subst;
   first [exact FPI|exact FOI|intros pos Range;apply KeepI;first [apply FK|apply FT];exact Range]. }
 assert (TablesI:forall h,elements_taptweak_generator_table_state h mi) by (intro h;eapply elements_taptweak_generator_readonly;[apply Tables|exact ReadI]).
 assert (SplitI:elements_taptweak_split_ready mi) by (eapply elements_taptweak_split_readonly;[exact Split|exact ReadI]).
 assert (BetaI:elements_taptweak_beta_initialized mi) by (eapply elements_taptweak_beta_initialized_preserved;[exact Beta|exact ReadI]).
 assert (ReadyI:elements_taptweak_modinfo_fe_state mi).
 { eapply elements_taptweak_modinfo_readonly;[exact Ready|exact ReadI]. }
 assert (InputI:scalar_at mi bt 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) (@canonical_scalar_normalize Simplicity.Alg.CoreFunSem ng))))).
 { eapply scalar_at_lframe;[exact InputNG|exact FrameI|intros;exact I]. }
 assert (XI:fe_at mi bk 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameI|intros;exact I]).
 assert (YI:fe_at mi bk 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameI|intros;exact I]).
 assert (FlagI:Mem.load Mint32 mi bk 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameI Mint32 bk 80 VK);[exact KeyFlag|intros;exact I]. }
 pose (e:=eckey_tweak_env bp bo);pose (le:=eckey_tweak_temps bk bt).
 destruct (exec_elements_taptweak_eckey_prepare Clear ng ax ay x y le mi bp bo bk bt eq_refl eq_refl
  Separate OwnedI TablesI SplitI BetaI ReadyI InputI BX BY XI YI FlagI TX TY Curve)
 as (mp & ox & oy & oz & Prepare & XP & YP & ZP & BXO & BYO & BZO & Literal & FlagP & OwnedP & ReadyP & FrameP & ForwardP & ReadP).
 pose (infinite:=eckey_tweak_infinite ng ax ay).
 assert (InfEq:Simplicity.Bit.toBool (@literal_gej_is_infinity Simplicity.Alg.CoreFunSem
  ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz))=infinite).
 { unfold infinite,eckey_tweak_infinite;rewrite Literal;reflexivity. }
 rewrite InfEq in FlagP.
 destruct (exec_elements_taptweak_eckey_finish Count e le mp bp bk ox oy oz infinite eq_refl eq_refl eq_refl eq_refl
  ltac:(distinct Separate) BXO BYO BZO XP YP ZP FlagP ReadyP
  (OwnedP bp 128 ltac:(clear;cbn [In];tauto)) (OwnedP bk 88 ltac:(clear;cbn [In];tauto)))
 as (mb & Finish & Affine & FPB & FKB & FrameB & ReadB).
 assert (FOB:Mem.range_perm mb bo 0 32 Cur Freeable).
 { eapply curve_keep_free;[lia|apply OwnedP;clear;cbn [In];tauto|exact FrameB|intros;split;distinct Separate]. }
 assert (FTB:Mem.range_perm mb bt 0 32 Cur Freeable).
 { eapply curve_keep_free;[lia|apply OwnedP;clear;cbn [In];tauto|exact FrameB|intros;split;distinct Separate]. }
 assert (PayloadB:eckey_tweak_key_result (eckey_tweak_value ng ax ay) mb bk).
 { unfold eckey_tweak_value;fold infinite;destruct infinite eqn:Inf;[exact I|].
   destruct (Affine eq_refl) as (xo & yo & XO & YO & BXX & BYY & Flag & Value).
   exists xo,yo;split;[exact XO|];split;[exact YO|];split;[exact BXX|];split;[exact BYY|];split;[exact Flag|].
   rewrite <-Literal;exact Value. }
 destruct (elements_taptweak_eckey_free mb bp bo PO FPB FOB) as (mf & Free & FrameF & ReadF).
 assert (Forward:mem_forward m mf).
 { eapply mem_forward_trans;[exact (proj1 ReadI)|];eapply mem_forward_trans;[exact ForwardP|];
   eapply mem_forward_trans;[exact (proj1 ReadB)|exact (proj1 ReadF)]. }
 assert (Frame:lframe (fun b _=>b<>bk /\b<>bt) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bk /\b<>bt).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameI|intros;exact I].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameP|intros b pos [Old [K T]] Valid;destruct (Fresh b Old);repeat split;assumption].
       * eapply lframe_trans.
         -- eapply lframe_implies;[exact FrameB|intros b pos [Old [K T]] Valid;destruct (Fresh b Old);split;assumption].
         -- eapply lframe_implies;[exact FrameF|intros b pos [Old [K T]] Valid;exact (Fresh b Old)].
   - intros b pos [K T] Old;repeat split;assumption. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=PTree.set _t'1 (Vint (bit_int infinite)) le)
   (m1:=mi) (m2:=mb) (out:=Out_return (Some (Vint (bit_int (negb infinite)),tint))).
   + exact Entry.
   + eapply elements_taptweak_eckey_prepare_then_finish;[exact Prepare|exact Finish].
   + split;[clear;discriminate|reflexivity].
   + exact Free.
 - split.
   + eapply eckey_tweak_key_framed;[exact PayloadB|exact FrameF|intros;exact (Fresh bk VK)].
   + split.
     * eapply curve_keep_free;[lia|exact FKB|exact FrameF|intros;exact (Fresh bk VK)].
     * split.
       -- eapply curve_keep_free;[lia|exact FTB|exact FrameF|intros;exact (Fresh bt VT)].
       -- split;[exact Frame|];split;[exact Forward|].
          split.
          ++ eapply elements_taptweak_modinfo_readonly;[exact Ready|].
             eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadP|];
             eapply preserved_trans;[exact ReadB|exact ReadF].
          ++ eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadP|];
             eapply preserved_trans;[exact ReadB|exact ReadF].
Qed.
