(** Original verifier call, with every signature value and all nine frees. *)
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
Require Import C.jet_secp_schnorr_verify_entry C.jet_secp_schnorr_verify_checks C.jet_secp_schnorr_signature_ranges C.jet_secp_xonly_parse_control.
Theorem eval_schnorrsig_verify_owned (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk msg r s ax ay:Ty.tySem (Word 8)) w m bsig bmsg bkey:
 bsig<>bmsg ->bsig<>bkey ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes s)) ->
 schnorr_bytes_at m bmsg Ptrofs.zero (schnorr_word_bytes msg) ->
 affine_storage_readable m bkey 0 w ->field_storage_value w=@toZ (WordToZ 8) pk ->
 field_storage_value (fun i=>w (4+i)%nat)=@toZ (WordToZ 8) ay ->
 @toZ (WordToZ 8) pk<feP ->@literal_decompress Simplicity.Alg.CoreFunSem (inl tt,pk)=inr (ax,ay) ->
 secp_sha_startup m ->(forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_verify)
 [Vptr bsig Ptrofs.zero;Vptr bmsg Ptrofs.zero;Vlong (Int64.repr 32);Vptr bkey Ptrofs.zero] E0 mf
 (Vint (bit_int (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))))) /\
 Mem.range_perm mf bsig 0 64 Cur Freeable /\lframe (fun b _=>b<>bsig) m mf /\mem_forward m mf.
Proof.
 intros SigMsg SigKey SigFree RInput SInput MsgBytes KeyInput KeyX KeyY PKBound Decode Startup Tables Split Beta Ready.
 assert (VS:Mem.valid_block m bsig) by (eapply Mem.perm_valid_block;apply (SigFree 0);clear;lia).
 assert (VM:Mem.valid_block m bmsg) by (eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;clear;lia|exact MsgBytes]).
 assert (VK:Mem.valid_block m bkey).
 { destruct KeyInput as (_ & _ & _ & Read & _);eapply Mem.perm_valid_block;apply (Read 0);clear;lia. }
 destruct (schnorr_verify_entry m (Vptr bsig Ptrofs.zero) (Vptr bmsg Ptrofs.zero) (Vptr bkey Ptrofs.zero))
 as (mi & bp & bk & ba & bng & br & bx & bpk & bbuf & bf & Entry & Separate & Fresh & Owned & FrameI & KeepI & ReadI).
 pose (e:=schnorr_verify_env bp bk ba bng br bx bpk bbuf bf).
 pose (le:=schnorr_verify_temps (Vptr bsig Ptrofs.zero) (Vptr bmsg Ptrofs.zero) (Vptr bkey Ptrofs.zero)).
 pose (li:=schnorr_verify_checked_temps le).
 assert (RInputI:uint8_array_at mi bsig 0 (map Int.repr (xonly_input_bytes r))).
 { intros i x Nth;rewrite (proj1 FrameI Mint8unsigned bsig (0+Z.of_nat i) VS);[apply RInput;exact Nth|intros;exact I]. }
 assert (SInputI:uint8_array_at mi bsig 32 (map Int.repr (xonly_input_bytes s))).
 { intros i x Nth;rewrite (proj1 FrameI Mint8unsigned bsig (32+Z.of_nat i) VS);[apply SInput;exact Nth|intros;exact I]. }
 assert (MsgI:schnorr_bytes_at mi bmsg Ptrofs.zero (schnorr_word_bytes msg)).
 { eapply schnorr_bytes_framed;[exact FrameI|exact VM|intros;exact I|exact MsgBytes]. }
 assert (KeyI:affine_storage_readable mi bkey 0 w).
 { eapply affine_storage_readable_lframe;[exact KeyInput|exact FrameI|intros;exact I]. }
 assert (SigFreeI:Mem.range_perm mi bsig 0 64 Cur Freeable).
 { intros pos Range;apply KeepI,SigFree;exact Range. }
 assert (ValidS:Mem.weak_valid_pointer mi bsig 0=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   eapply Mem.perm_implies;[apply SigFreeI;clear;lia|constructor]. }
 assert (ValidM:Mem.weak_valid_pointer mi bmsg 0=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   pose proof (Mem.load_valid_access _ _ _ _ _ (MsgI 0%nat ltac:(rewrite schnorr_word_bytes_length;clear;lia))) as [Perm _].
   eapply Mem.perm_implies;[apply (Perm 0);clear;change (0<=0<0+1);lia|constructor]. }
 assert (ValidK:Mem.weak_valid_pointer mi bkey 0=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   destruct KeyI as (_ & _ & _ & Perm & _);eapply Mem.perm_implies;[apply (Perm 0);clear;lia|constructor]. }
 assert (StartupI:secp_sha_startup mi).
 { eapply secp_sha_startup_preserved;[exact Startup|exact ReadI|exact FrameI|intros;exact I]. }
 assert (ReadyI:modinfo_fe_state mi).
 { eapply modinfo_fe_state_unchanged;[exact Ready|].
   eapply Mem.unchanged_on_implies;[exact (proj2 ReadI)|].
   intros b pos Same _;subst b;split;[exact (proj1 (proj1 Ready))|exact (proj2 Ready pos)]. }
 assert (TablesI:forall h,generator_table_state h mi) by (eapply generator_tables_readonly;[exact Tables|exact ReadI]).
 assert (SplitI:split_constants_ready mi) by (eapply split_constants_readonly;[exact Split|exact ReadI]).
 assert (BetaI:beta_initialized mi) by (eapply beta_initialized_preserved;[exact Beta|exact ReadI]).
 pose proof (exec_schnorr_signature_return_all Copy Clear Count w e li mi bp bk ba bng br bx bpk bf
  s ax ay r pk msg bsig bmsg Ptrofs.zero bbuf bkey 0) as Run.
 specialize (Run eq_refl eq_refl KeyI KeyX KeyY eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  ltac:(clear;change (32<=18446744073709551615);lia) eq_refl eq_refl eq_refl SigFreeI RInputI SInputI MsgI StartupI).
 specialize (Run eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Separate).
 assert (OldSig:~In bsig [bp;bk;ba;bng;br;bx;bpk;bbuf;bf]) by (apply Fresh;exact VS).
 assert (OldMsg:~In bmsg [bp;bk;ba;bng;br;bx;bpk;bbuf;bf]) by (apply Fresh;exact VM).
 assert (OldKey:~In bkey [bp;bk;ba;bng;br;bx;bpk;bbuf;bf]) by (apply Fresh;exact VK).
 specialize (Run OldSig ltac:(clear -OldMsg;cbn [In] in *;tauto)
  ltac:(clear -OldMsg SigMsg;cbn [In] in *;intuition congruence)
  ltac:(clear -OldKey SigKey;cbn [In] in *;intuition congruence)
  Owned TablesI SplitI BetaI ReadyI PKBound Decode).
 destruct Run as (mb & lef & Suffix & OwnedB & SigFreeB & FrameB & ForwardB).
 assert (Checks:Clight2.exec_stmt secp_ge e le mi (statement_sequence schnorr_verify_checks Sskip) E0 li mi Out_normal).
 { apply exec_schnorr_verify_checks with (bsig:=bsig) (bmsg:=bmsg) (omsg:=Ptrofs.zero) (bkey:=bkey) (okey:=Ptrofs.zero);
   try reflexivity.
   - exact ValidS.
   - exact ValidM.
   - exact ValidK. }
 destruct (free_list_exists [(bf,0,4);(bng,0,32);(bk,0,32);(bpk,0,88);(ba,0,128);(bbuf,0,32);(br,0,88);(bx,0,40);(bp,0,128)] mb)
 as (mf & Frees & UnchangedF).
 - clear -Separate;unfold schnorr_verify_locals in Separate;repeat rewrite NoDup_cons_iff in *;cbn [fst In] in *;
   repeat constructor;cbn [fst In];intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;
   inversion Slot;subst b lo hi;apply OwnedB;clear;cbn [In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bp;bk;ba;bng;br;bx;bpk;bbuf;bf]) mb mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside _;clear -Outside;cbn [map fst In] in *;tauto. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
     (out:=Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
      (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))))),tint))).
     * exact Entry.
     * rewrite schnorr_verify_checks_source;eapply exec_statement_prefix_then_last;[exact Checks|exact Suffix].
     * split;[clear;discriminate|reflexivity].
     * unfold e;rewrite schnorr_verify_blocks;exact Frees.
   + split.
     * eapply curve_keep_free;[clear;lia|exact SigFreeB|exact FrameF|intros;exact OldSig].
     * split.
       -- eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bsig).
          ++ eapply lframe_trans.
             ** eapply lframe_implies;[exact FrameI|intros;exact I].
             ** eapply lframe_trans.
                --- eapply lframe_implies;[exact FrameB|].
                    intros b pos [Old NotSig] _;clear -Fresh Old NotSig;
                     pose proof (Fresh b Old);unfold schnorr_verify_locals in H;cbn [In] in *;intuition.
                --- eapply lframe_implies;[exact FrameF|].
                    intros b pos [Old _] _;apply Fresh;exact Old.
          ++ intros b pos Other Valid;split;assumption.
       -- eapply mem_forward_trans;[exact (proj1 ReadI)|].
          eapply mem_forward_trans;[exact ForwardB|eapply freelist_forward;exact Frees].
Qed.
