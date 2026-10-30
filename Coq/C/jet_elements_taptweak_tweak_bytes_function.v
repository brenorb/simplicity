(** Whole linked byte-scalar tweak helper, including overflow and native failure. *)
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
Require Import C.jet_secp_eckey_tweak_function C.jet_secp_tweak_bytes_entry C.jet_secp_tweak_bytes_calls
 C.jet_secp_scalar_set_canonical C.jet_secp_scalar_set_flag C.jet_secp_xonly_parse_field
 C.jet_secp_scalar_set_flag_frame C.jet_read8s_layout C.jet_sx_expr C.jet_sx_state
 C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_tweak_bytes_function C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_beta
 C.jet_elements_taptweak_curve_transport.
Require Import C.jet_elements_taptweak_eckey_function C.jet_elements_taptweak_tweak_bytes_entry C.jet_elements_taptweak_tweak_bytes_calls.
Local Opaque secp_ge elements_taptweak_ge eckey_tweak_point literal_gej_norm literal_gej_is_infinity rescale_field_output.
Theorem eval_elements_taptweak_bytes_helper (Clear:memset_model) (Count:ctz_model)
 (ng ax ay:Ty.tySem (Word 8)) x y m bk bb:
 bk<>bb ->Mem.range_perm m bk 0 88 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 (forall h,elements_taptweak_generator_table_state h m) ->elements_taptweak_split_ready m ->elements_taptweak_beta_initialized m ->elements_taptweak_modinfo_fe_state m ->
 uint8_array_at m bb 0 (map Int.repr (xonly_input_bytes ng)) ->
 square_input_bounds x ->square_input_bounds y ->fe_at m bk 0 (words5 x) ->fe_at m bk 40 (words5 y) ->Mem.load Mint32 m bk 80=Some (Vint Int.zero) ->
 table_word_literal x ax ->table_word_literal y ay ->Simplicity.Bit.toBool (@literal_ge_is_on_curve Simplicity.Alg.CoreFunSem (ax,ay))=true ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ec_pubkey_tweak_add_helper)
 [Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (bit_int (tweak_bytes_result ng ax ay))) /\
 eckey_tweak_key_result (tweak_bytes_value ng ax ay) mf bk /\
 Mem.range_perm mf bk 0 88 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bk /\b<>bb) m mf /\mem_forward m mf /\elements_taptweak_modinfo_fe_state mf /\readonly_preserved m mf.
Proof.
 intros KB FK FB Tables Split Beta Ready Bytes BX BY X Y KeyFlag TX TY Curve.
 assert (VK:Mem.valid_block m bk) by (eapply Mem.perm_valid_block;apply (FK 0);lia).
 assert (VB:Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
 destruct (elements_taptweak_tweak_bytes_entry m bk bb) as (mi & bt & bf & Entry & TF & Fresh & FTI & FFI & FrameI & KeepI & ReadI).
 assert (KT:bk<>bt) by (exact (proj1 (Fresh bk VK))).
 assert (KF:bk<>bf) by (exact (proj2 (Fresh bk VK))).
 assert (BT:bb<>bt) by (exact (proj1 (Fresh bb VB))).
 assert (BF:bb<>bf) by (exact (proj2 (Fresh bb VB))).
 pose (e:=tweak_bytes_env bt bf);pose (le:=tweak_bytes_temps bk bb).
 assert (Access:Mem.valid_access mi Mint32 bf 0 Writable).
 { split;[intros pos Range;eapply Mem.perm_implies;[apply FFI;exact Range|constructor]|exists 0;reflexivity]. }
 destruct (Mem.valid_access_store mi Mint32 bf 0 (Vint Int.zero) Access) as (mz & Store).
 assert (Init:Clight2.exec_stmt elements_taptweak_ge e le mi tweak_bytes_init E0 le mz Out_normal).
 { eapply exec_elements_taptweak_bytes_init;[reflexivity|exact Store]. }
 assert (FrameZ:lframe (fun b _=>b<>bf) mi mz).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|intros;congruence]. }
 assert (KeepZ:keeps_permissions mi mz).
 { intros b pos k p Perm;eapply Mem.perm_store_1;[exact Store|exact Perm]. }
 assert (ReadZ:readonly_preserved mi mz) by (eapply store_preserved;exact Store).
 assert (FTZ:Mem.range_perm mz bt 0 32 Cur Freeable) by (intros pos Range;apply KeepZ,FTI;exact Range).
 assert (FFZ:Mem.range_perm mz bf 0 4 Cur Freeable) by (intros pos Range;apply KeepZ,FFI;exact Range).
 assert (FBZ:Mem.range_perm mz bb 0 32 Cur Freeable) by (intros pos Range;apply KeepZ,KeepI,FB;exact Range).
 assert (BytesZ:uint8_array_at mz bb 0 (map Int.repr (xonly_input_bytes ng))).
 { intros i v Nth;rewrite (proj1 FrameZ Mint8unsigned bb (0+Z.of_nat i));[| |intros;exact BF].
   - rewrite (proj1 FrameI Mint8unsigned bb (0+Z.of_nat i) VB);[apply Bytes;exact Nth|intros;exact I].
   - exact (proj1 (proj1 ReadI bb VB)). }
 destruct (eval_scalar_set_b32_canonical_flag ng bt bb 0 bf mz
  ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(lia)
  ltac:(clear;change (32<=18446744073709551615);lia) FTZ
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply FBZ;exact Range|constructor]) FFZ BytesZ)
 as (mp & ParseCall & Scalar & Overflow & KeepParse & FrameParse & ReadParse).
 fold (tweak_bytes_overflow ng) in Overflow.
 pose proof(elements_taptweak_curve_transport _ _ mz _ E0 mp _ elements_taptweak_has_scalar_set_b32 ParseCall)as ParseCallT.
 assert (Parse:Clight2.exec_stmt elements_taptweak_ge e le mz tweak_bytes_parse E0 le mp Out_normal).
 { eapply exec_elements_taptweak_bytes_parse;try reflexivity;exact ParseCallT. }
 assert (KeepP:keeps_permissions m mp).
 { eapply keeps_permissions_trans;[exact KeepI|];eapply keeps_permissions_trans;[exact KeepZ|exact KeepParse]. }
 assert (ReadP:readonly_preserved m mp).
 { eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadZ|exact ReadParse]. }
 assert (FrameP:lframe (fun b _=>b<>bb) m mp).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bb).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameI|intros;exact I].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameZ|intros b pos [Old NB] Valid;exact (proj2 (Fresh b Old))].
       * eapply lframe_implies;[exact FrameParse|].
         intros b pos [Old NB] Valid;destruct (Fresh b Old) as [NT NF];split;[apply scalar_flag_foot_outside;repeat split;congruence|exact NF].
   - intros b pos NB Old;split;assumption. }
 assert (ReadyP:elements_taptweak_modinfo_fe_state mp).
 { eapply elements_taptweak_modinfo_readonly;[exact Ready|exact ReadP]. }
 assert (FTParse:Mem.range_perm mp bt 0 32 Cur Freeable) by (intros pos Range;apply KeepParse,FTZ;exact Range).
 assert (FFParse:Mem.range_perm mp bf 0 4 Cur Freeable) by (intros pos Range;apply KeepParse,FFZ;exact Range).
 assert (FKParse:Mem.range_perm mp bk 0 88 Cur Freeable) by (intros pos Range;apply KeepP,FK;exact Range).
 assert (FBParse:Mem.range_perm mp bb 0 32 Cur Freeable) by (intros pos Range;apply KeepP,FB;exact Range).
 assert (NativeBranch:exists mb,
  Clight2.exec_stmt elements_taptweak_ge e le mp tweak_bytes_guard E0
   (tweak_bytes_guard_temps le (tweak_bytes_overflow ng) (negb (eckey_tweak_infinite ng ax ay))) mb Out_normal /\
  eckey_tweak_key_result (tweak_bytes_value ng ax ay) mb bk /\
  Mem.range_perm mb bk 0 88 Cur Freeable /\Mem.range_perm mb bb 0 32 Cur Freeable /\
  Mem.range_perm mb bt 0 32 Cur Freeable /\Mem.range_perm mb bf 0 4 Cur Freeable /\
  lframe (fun b _=>b<>bk /\b<>bt) mp mb /\mem_forward mp mb /\elements_taptweak_modinfo_fe_state mb /\readonly_preserved mp mb).
 { destruct (tweak_bytes_overflow ng) eqn:Over.
   - exists mp;split.
     + apply exec_elements_taptweak_bytes_guard_reject with (bf:=bf);[reflexivity|exact Overflow].
     + unfold tweak_bytes_value;rewrite Over;split;[exact I|];split;[exact FKParse|];split;[exact FBParse|];split;[exact FTParse|];split;[exact FFParse|];
       split;[apply lframe_refl|];split;[apply mem_forward_refl|];split;[exact ReadyP|apply preserved_refl].
   - assert (XP:fe_at mp bk 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameP|intros;exact KB]).
     assert (YP:fe_at mp bk 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameP|intros;exact KB]).
     assert (FlagP:Mem.load Mint32 mp bk 80=Some (Vint Int.zero)).
     { rewrite (proj1 FrameP Mint32 bk 80 VK);[exact KeyFlag|intros;exact KB]. }
     assert (TablesP:forall h,elements_taptweak_generator_table_state h mp) by (intro h;eapply elements_taptweak_generator_readonly;[apply Tables|exact ReadP]).
     assert (SplitP:elements_taptweak_split_ready mp) by (eapply elements_taptweak_split_readonly;[exact Split|exact ReadP]).
     assert (BetaP:elements_taptweak_beta_initialized mp) by (eapply elements_taptweak_beta_initialized_preserved;[exact Beta|exact ReadP]).
     destruct (eval_elements_taptweak_eckey_pubkey_tweak_add Clear Count ng ax ay x y mp bk bt KT FKParse FTParse
      TablesP SplitP BetaP ReadyP Scalar BX BY XP YP FlagP TX TY Curve)
      as (mb & Native & Payload & FKB & FTB & FrameB & ForwardB & ReadyB & ReadB).
     exists mb;split.
     + eapply exec_elements_taptweak_bytes_guard_accept with (bt:=bt) (bk:=bk) (bf:=bf);try reflexivity;
       [exact Overflow|exact Native].
     + unfold tweak_bytes_value;rewrite Over;split;[exact Payload|];split;[exact FKB|];split.
       * eapply curve_keep_free;[clear;lia|exact FBParse|exact FrameB|intros;clear -KB BT;split;congruence].
       * split;[exact FTB|];split.
         -- eapply curve_keep_free;[clear;lia|exact FFParse|exact FrameB|intros;clear -KF TF;split;congruence].
         -- split;[exact FrameB|];split;[exact ForwardB|];split;assumption. }
 destruct NativeBranch as (mb & Guard & PayloadB & FKB & FBB & FTB & FFB & FrameB & ForwardB & ReadyB & ReadB).
 destruct (elements_taptweak_tweak_bytes_free mb bt bf TF FTB FFB) as (mf & Free & FrameF & ReadF).
 assert (Forward:mem_forward m mf).
 { eapply mem_forward_trans;[exact (proj1 ReadP)|];eapply mem_forward_trans;[exact ForwardB|exact (proj1 ReadF)]. }
 assert (Frame:lframe (fun b _=>b<>bk /\b<>bb) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bk /\b<>bb).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameP|intros b pos [Old [NK NB]] Valid;exact NB].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FrameB|intros b pos [Old [NK NB]] Valid;split;[exact NK|exact (proj1 (Fresh b Old))]].
       * eapply lframe_implies;[exact FrameF|intros b pos [Old [NK NB]] Valid;exact (Fresh b Old)].
   - intros b pos [NK NB] Old;repeat split;assumption. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le)
   (le2:=tweak_bytes_guard_temps le (tweak_bytes_overflow ng) (negb (eckey_tweak_infinite ng ax ay)))
   (m1:=mi) (m2:=mb) (out:=Out_return (Some (Vint (bit_int (tweak_bytes_result ng ax ay)),tint))).
   + exact Entry.
   + rewrite tweak_bytes_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Init|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Parse|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Guard|apply exec_elements_taptweak_bytes_return].
   + split;[clear;discriminate|reflexivity].
   + exact Free.
 - split.
   + eapply eckey_tweak_key_framed;[exact PayloadB|exact FrameF|intros;exact (Fresh bk VK)].
   + split.
     * eapply curve_keep_free;[clear;lia|exact FKB|exact FrameF|intros;exact (Fresh bk VK)].
     * split.
       -- eapply curve_keep_free;[clear;lia|exact FBB|exact FrameF|intros;exact (Fresh bb VB)].
       -- split;[exact Frame|];split;[exact Forward|].
          split.
          ++ eapply elements_taptweak_modinfo_readonly;[exact ReadyB|exact ReadF].
          ++ eapply preserved_trans;[exact ReadP|];eapply preserved_trans;[exact ReadB|exact ReadF].
Qed.
