(** Complete original public CheckSig wrapper, all inputs and both key-parser exits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_frame_inv C.jet_buffer_input C.jet_readBit_layout C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_root_chain_owned C.jet_secp_statement_prefix
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve
 C.jet_secp_schnorr_verify_literal C.jet_secp_schnorr_signature_guards C.jet_secp_schnorr_startup
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control
 C.jet_secp_bip0340_function C.jet_secp_bip0340_public_parse C.jet_secp_checksig_public_entry C.jet_secp_checksig_public_read C.jet_secp_checksig_after_parse
 C.jet_secp_checksig_tag C.jet_secp_checksig_hash C.jet_secp_schnorr_challenge_hash.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_bip0340_check Translate.encode.

Theorem eval_checksig_public (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk ir h r s:Ty.tySem (Word 8)) v_env m0 bd base bs sbase bi edge cursor:
 checksig_startup m0 ->frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge cursor ->
 frame_input_cells_at m0 bi edge cursor (Translate.encode pk) ->
 frame_input_cells_at m0 bi edge (cursor+256) (@Translate.encode (Word 9) (ir,h)) ->
 frame_input_cells_at m0 bi edge (cursor+768) (@Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s)) ->
 0<=cursor ->cursor+1280<=Int64.max_unsigned ->exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_check_sig_verify)
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf
 (Vint (bit_int (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s)))))) /\
 lframe (fun _ _=>True) m0 mf /\mem_forward m0 mf /\checksig_startup mf.
Proof.
 intros Ready Base Align Source KeyInput MsgInput SigInput Cursor Max.
 destruct (checksig_public_entry v_env m0 bd base bs sbase)
 as (mi & bl & bb & bkey & bmsg & bsig & bout & bctx & bres & Entry & Separate & Fresh & OwnedI & FrameI & KeepI & ReadI).
 pose (e:=checksig_public_env bl bb bkey bmsg bsig bout bctx bres).
 pose (le:=checksig_public_temps v_env bd base bs sbase).
 destruct (checksig_public_prepare pk le m0 mi bl bb bkey bmsg bsig bout bctx bres bs sbase bi edge cursor
  Separate Fresh OwnedI FrameI ReadI eq_refl Base Align Source KeyInput Cursor ltac:(lia))
 as (mr & Prefix & Bytes & Fields & OwnedR & FrameR & ReadR).
 destruct (exec_bip0340_public_parse Copy Clear pk e le mr bkey bb eq_refl eq_refl eq_refl
  ltac:(clear -Separate;unfold checksig_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence)
  (OwnedR bkey 64 ltac:(clear;cbn [checksig_public_storage In];tauto))
  (OwnedR bb 32 ltac:(clear;cbn [checksig_public_storage In];tauto)) Bytes)
 as (mp & Guard & Parsed & FreeK & FreeB & FrameP & ReadP).
 pose (lp:=PTree.set _t'1 (Vint (xonly_parse_result pk)) le).
 assert (Outside:forall b,In b [bl;bmsg;bsig] ->b<>bkey /\b<>bb).
 { clear -Separate;intros b Member;unfold checksig_public_locals in Separate;
   repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (OwnedP:forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm mp b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [checksig_public_storage In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;subst b hi;
   first [exact FreeK|exact FreeB|eapply curve_keep_free;
    [clear;lia|apply OwnedR;clear;cbn [checksig_public_storage In];tauto|exact FrameP|
     intros;clear -Separate;unfold checksig_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence]]. }
 assert (FramePAll:lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) mr mp).
 { eapply lframe_implies;[exact FrameP|];intros b pos Out _;clear -Out;cbn [checksig_public_locals In] in *;intuition congruence. }
 assert (Frame0P:lframe (fun _ _=>True) m0 mp) by (eapply bip0340_old_frame;[exact Fresh|exact FrameR|exact FramePAll]).
 assert (Forward0P:mem_forward m0 mp) by (eapply mem_forward_trans;[exact (proj1 ReadR)|exact (proj1 ReadP)]).
 assert (ReadyP:checksig_startup mp) by (eapply checksig_startup_framed;[exact Ready|exact Forward0P|exact Frame0P]).
 assert (FieldsP:frame_fields_at mp bl 0 bi edge (cursor+256)).
 { eapply bip0340_source_fields_framed;[exact Fields|exact FrameP|intros;apply Outside;clear;cbn [In];tauto]. }
 assert (MsgP:frame_input_cells_at mp bi edge (cursor+256) (@Translate.encode (Word 9) (ir,h))).
 { eapply buffer_input_cells_preserved;[|exact MsgInput].
   intros ofs w Load;rewrite (proj1 Frame0P Mint64 bi ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact I]. }
 assert (SigP:frame_input_cells_at mp bi edge (cursor+768) (@Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s))).
 { eapply buffer_input_cells_preserved;[|exact SigInput].
   intros ofs w Load;rewrite (proj1 Frame0P Mint64 bi ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact I]. }
 assert (VI:Mem.valid_block m0 bi).
 { pose proof (proj1 (frame_input_byte_list m0 bi edge cursor (vector_values (Word 3) 5 pk))) as Get.
   assert (Encoded:frame_input_cells_at m0 bi edge cursor
    (concat (map (@Translate.encode (Word 3)) (vector_values (Word 3) 5 pk))))
    by (rewrite <-encode_vector_values;exact KeyInput).
   specialize (Get Encoded);destruct (vector_values (Word 3) 5 pk) as [|x xs] eqn:BytesV.
   - pose proof (vector_values_length (Word 3) 5 pk);rewrite BytesV in H;discriminate H.
   - pose proof (Get 0%nat x eq_refl) as Bits.
     specialize (Bits 0%nat (Z.testbit (@toZ (WordToZ 3) x) 7) eq_refl).
     destruct Bits as (_ & _ & w & Load & _);eapply load_valid;exact Load. }
 assert (InputSeparate:~In bi (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) by (apply Fresh;exact VI).
 assert (Rest:exists mb lef,
 Clight2.exec_stmt secp_ge e le mr (root_drop_statements 2 (fn_body f_simplicity_check_sig_verify)) E0 lef mb
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s))))),tint))) /\
 (forall b hi,In (b,hi) (checksig_public_storage bl bb bkey bmsg bsig bout bctx bres) ->Mem.range_perm mb b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b (checksig_public_locals bl bb bkey bmsg bsig bout bctx bres)) mr mb /\mem_forward mr mb).
 { destruct (xonly_parse_result_cases pk) as [Zero|One].
   - exists mp,lp;split.
     + rewrite (schnorr_spec_reject_pubkey pk (checksig_hash_word ir h) r s Zero),check_sig_public_parse_source.
       eapply exec_Sseq_2;[|clear;discriminate].
       rewrite (bip0340_parse_zero_outcome pk Zero) in Guard;exact Guard.
     + split;[exact OwnedP|];split;[exact FramePAll|exact (proj1 ReadP)].
   - destruct (exec_checksig_after_parse Copy Clear Count pk ir h r s lp mp bl bb bkey bmsg bsig bout bctx bres bi edge cursor
      Separate InputSeparate
      Cursor Max OwnedP FieldsP MsgP SigP One Parsed ReadyP)
     as (mb & lef & Suffix & OwnedB & FrameB & ForwardB & ReadyB).
     exists mb,lef;split.
     + rewrite check_sig_public_parse_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=lp);[|exact Suffix].
       rewrite (bip0340_parse_one_outcome pk One) in Guard;exact Guard.
     + split;[exact OwnedB|];split.
       * eapply lframe_trans;[exact FramePAll|exact FrameB].
       * eapply mem_forward_trans;[exact (proj1 ReadP)|exact ForwardB]. }
 destruct Rest as (mb & lef & Rest & OwnedB & FrameB & ForwardB).
 assert (Frame0B:lframe (fun _ _=>True) m0 mb) by (eapply bip0340_old_frame;[exact Fresh|exact FrameR|exact FrameB]).
 destruct (checksig_public_free mb bl bb bkey bmsg bsig bout bctx bres Separate OwnedB) as (mf & Frees & FrameF & ReadF).
 assert (Frame:lframe (fun _ _=>True) m0 mf) by (eapply bip0340_old_frame;[exact Fresh|exact Frame0B|exact FrameF]).
 assert (Forward:mem_forward m0 mf).
 { eapply mem_forward_trans;[exact (proj1 ReadR)|];eapply mem_forward_trans;[exact ForwardB|exact (proj1 ReadF)]. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
   (out:=Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
    (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s))))),tint))).
   + exact Entry.
   + rewrite checksig_public_source;eapply bip0340_exec_two_then_last;[exact Prefix|exact Rest].
   + split;[clear;discriminate|destruct (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,checksig_hash_word ir h),(r,s))));reflexivity].
   + exact Frees.
 - split;[exact Frame|];split;[exact Forward|eapply checksig_startup_framed;[exact Ready|exact Forward|exact Frame]].
Qed.
