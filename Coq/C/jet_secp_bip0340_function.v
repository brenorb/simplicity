(** Complete original public BIP340 wrapper, all inputs and both key-parser exits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_frame_inv C.jet_buffer_input C.jet_readBit_layout C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_root_chain_owned C.jet_secp_statement_prefix
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve
 C.jet_secp_schnorr_verify_literal C.jet_secp_schnorr_signature_guards C.jet_secp_schnorr_startup
 C.jet_secp_xonly_parse_field C.jet_secp_xonly_parse_control
 C.jet_secp_bip0340_public_entry C.jet_secp_bip0340_public_read C.jet_secp_bip0340_public_parse C.jet_secp_bip0340_after_parse.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_bip0340_check Translate.encode.
Lemma bip0340_exec_two_then_last ge e le m a b last li mi lef mf out:
 Clight2.exec_stmt ge e le m (Ssequence a b) E0 li mi Out_normal ->
 Clight2.exec_stmt ge e li mi last E0 lef mf out ->
 Clight2.exec_stmt ge e le m (Ssequence a (Ssequence b last)) E0 lef mf out.
Proof.
 intros Prefix Rest;inversion Prefix;subst;try contradiction.
 match goal with H:?t1 ** ?t2=E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
 change E0 with (E0**E0);eapply exec_Sseq_1;[eassumption|].
 eapply exec_Sseq_1;[eassumption|exact Rest].
Qed.
Lemma bip0340_source_fields_framed m mf bl bi edge rc P:
 frame_fields_at m bl 0 bi edge rc ->lframe P m mf ->(forall pos,P bl pos) ->frame_fields_at mf bl 0 bi edge rc.
Proof.
 intros [Edge Cursor] Frame Outside;split.
 - rewrite (proj1 Frame Mptr bl 0 (load_valid _ _ _ _ _ Edge));[exact Edge|intros;apply Outside].
 - rewrite (proj1 Frame Mint64 bl (0+8) (load_valid _ _ _ _ _ Cursor));[exact Cursor|intros;apply Outside].
Qed.
Lemma bip0340_old_frame m0 m mf locals:
 (forall b,Mem.valid_block m0 b ->~In b locals) ->lframe (fun _ _=>True) m0 m ->
 lframe (fun b _=>~In b locals) m mf ->lframe (fun _ _=>True) m0 mf.
Proof.
 intros Fresh Old Step;eapply lframe_implies with (P:=fun b _=>Mem.valid_block m0 b).
 - eapply lframe_trans.
   + eapply lframe_implies;[exact Old|intros;exact I].
   + eapply lframe_implies;[exact Step|];intros b pos Valid _;apply Fresh;exact Valid.
 - intros b pos _ Valid;exact Valid.
Qed.
Lemma bip0340_parse_zero_outcome (pk:Ty.tySem (Word 8)):xonly_parse_result pk=Int.zero ->
 bip0340_parse_outcome pk=Out_return (Some (Vint Int.zero,tint)).
Proof. intro Zero;unfold bip0340_parse_outcome;rewrite Zero;reflexivity. Qed.
Lemma bip0340_parse_one_outcome (pk:Ty.tySem (Word 8)):xonly_parse_result pk=Int.one ->
 bip0340_parse_outcome pk=Out_normal.
Proof. intro One;unfold bip0340_parse_outcome;rewrite One;reflexivity. Qed.
Theorem eval_bip0340_public (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk msg r s:Ty.tySem (Word 8)) v_env m0 bd base bs sbase bi edge cursor:
 schnorr_startup m0 ->frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge cursor ->
 frame_input_cells_at m0 bi edge cursor (Translate.encode pk) ->
 frame_input_cells_at m0 bi edge (cursor+256) (Translate.encode msg) ->
 frame_input_cells_at m0 bi edge (cursor+512) (@Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s)) ->
 0<=cursor ->cursor+1024<=Int64.max_unsigned ->exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_bip_0340_verify)
 [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf
 (Vint (bit_int (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))))) /\
 lframe (fun _ _=>True) m0 mf /\mem_forward m0 mf /\schnorr_startup mf.
Proof.
 intros Ready Base Align Source KeyInput MsgInput SigInput Cursor Max.
 destruct (bip0340_public_entry v_env m0 bd base bs sbase)
 as (mi & bl & bb & bkey & bmsg & bsig & Entry & Separate & Fresh & OwnedI & FrameI & KeepI & ReadI).
 pose (e:=bip0340_public_env bl bb bkey bmsg bsig).
 pose (le:=bip0340_public_temps v_env bd base bs sbase).
 destruct (bip0340_public_prepare pk le m0 mi bl bb bkey bmsg bsig bs sbase bi edge cursor
  Separate Fresh OwnedI FrameI ReadI eq_refl Base Align Source KeyInput Cursor ltac:(lia))
 as (mr & Prefix & Bytes & Fields & OwnedR & FrameR & ReadR).
 destruct (exec_bip0340_public_parse Copy Clear pk e le mr bkey bb eq_refl eq_refl eq_refl
  ltac:(clear -Separate;unfold bip0340_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence)
  (OwnedR bkey 64 ltac:(clear;cbn [bip0340_public_storage In];tauto))
  (OwnedR bb 32 ltac:(clear;cbn [bip0340_public_storage In];tauto)) Bytes)
 as (mp & Guard & Parsed & FreeK & FreeB & FrameP & ReadP).
 pose (lp:=PTree.set _t'1 (Vint (xonly_parse_result pk)) le).
 assert (Outside:forall b,In b [bl;bmsg;bsig] ->b<>bkey /\b<>bb).
 { clear -Separate;intros b Member;unfold bip0340_public_locals in Separate;
   repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (OwnedP:forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm mp b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [bip0340_public_storage In] in Slot;
   destruct Slot as [Same|[Same|[Same|[Same|[Same|Bad]]]]];try contradiction;inversion Same;subst b hi.
   - eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [bip0340_public_storage In];tauto|exact FrameP|].
     intros;apply Outside;clear;cbn [In];tauto.
   - exact FreeB.
   - exact FreeK.
   - eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [bip0340_public_storage In];tauto|exact FrameP|].
     intros;apply Outside;clear;cbn [In];tauto.
   - eapply curve_keep_free;[clear;lia|apply OwnedR;clear;cbn [bip0340_public_storage In];tauto|exact FrameP|].
     intros;apply Outside;clear;cbn [In];tauto. }
 assert (FramePAll:lframe (fun b _=>~In b (bip0340_public_locals bl bb bkey bmsg bsig)) mr mp).
 { eapply lframe_implies;[exact FrameP|];intros b pos Out _;clear -Out;cbn [bip0340_public_locals In] in *;intuition congruence. }
 assert (Frame0P:lframe (fun _ _=>True) m0 mp) by (eapply bip0340_old_frame;[exact Fresh|exact FrameR|exact FramePAll]).
 assert (Forward0P:mem_forward m0 mp) by (eapply mem_forward_trans;[exact (proj1 ReadR)|exact (proj1 ReadP)]).
 assert (ReadyP:schnorr_startup mp) by (eapply schnorr_startup_framed;[exact Ready|exact Forward0P|exact Frame0P]).
 assert (FieldsP:frame_fields_at mp bl 0 bi edge (cursor+256)).
 { eapply bip0340_source_fields_framed;[exact Fields|exact FrameP|intros;apply Outside;clear;cbn [In];tauto]. }
 assert (MsgP:frame_input_cells_at mp bi edge (cursor+256) (Translate.encode msg)).
 { eapply buffer_input_cells_preserved;[|exact MsgInput].
   intros ofs w Load;rewrite (proj1 Frame0P Mint64 bi ofs (load_valid _ _ _ _ _ Load));[exact Load|intros;exact I]. }
 assert (SigP:frame_input_cells_at mp bi edge (cursor+512) (@Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s))).
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
 assert (InputSeparate:bl<>bi /\bmsg<>bi /\bsig<>bi).
 { pose proof (Fresh bi VI);unfold bip0340_public_locals in H;cbn [In] in *;intuition congruence. }
 assert (Rest:exists mb lef,
 Clight2.exec_stmt secp_ge e le mr (root_drop_statements 2 (fn_body f_simplicity_bip_0340_verify)) E0 lef mb
  (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
   (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))))),tint))) /\
 (forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm mb b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b (bip0340_public_locals bl bb bkey bmsg bsig)) mr mb /\mem_forward mr mb).
 { destruct (xonly_parse_result_cases pk) as [Zero|One].
   - exists mp,lp;split.
     + rewrite (schnorr_spec_reject_pubkey pk msg r s Zero),bip0340_public_parse_source.
       eapply exec_Sseq_2;[|clear;discriminate].
       rewrite (bip0340_parse_zero_outcome pk Zero) in Guard;exact Guard.
     + split;[exact OwnedP|];split;[exact FramePAll|exact (proj1 ReadP)].
   - destruct (exec_bip0340_after_parse Copy Clear Count pk msg r s lp mp bl bb bkey bmsg bsig bi edge cursor
      Separate (proj1 InputSeparate) (proj1 (proj2 InputSeparate)) (proj2 (proj2 InputSeparate))
      Cursor Max OwnedP FieldsP MsgP SigP One Parsed ReadyP)
     as (mb & lef & Suffix & OwnedB & FrameB & ForwardB & ReadyB).
     exists mb,lef;split.
     + rewrite bip0340_public_parse_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=lp);[|exact Suffix].
       rewrite (bip0340_parse_one_outcome pk One) in Guard;exact Guard.
     + split;[exact OwnedB|];split.
       * eapply lframe_trans;[exact FramePAll|exact FrameB].
       * eapply mem_forward_trans;[exact (proj1 ReadP)|exact ForwardB]. }
 destruct Rest as (mb & lef & Rest & OwnedB & FrameB & ForwardB).
 assert (Frame0B:lframe (fun _ _=>True) m0 mb) by (eapply bip0340_old_frame;[exact Fresh|exact FrameR|exact FrameB]).
 destruct (bip0340_public_free mb bl bb bkey bmsg bsig Separate OwnedB) as (mf & Frees & FrameF & ReadF).
 assert (Frame:lframe (fun _ _=>True) m0 mf) by (eapply bip0340_old_frame;[exact Fresh|exact Frame0B|exact FrameF]).
 assert (Forward:mem_forward m0 mf).
 { eapply mem_forward_trans;[exact (proj1 ReadR)|];eapply mem_forward_trans;[exact ForwardB|exact (proj1 ReadF)]. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
   (out:=Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
    (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))))),tint))).
   + exact Entry.
   + rewrite bip0340_public_source;eapply bip0340_exec_two_then_last;[exact Prefix|exact Rest].
   + split;[clear;discriminate|destruct (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))));reflexivity].
   + exact Frees.
 - split;[exact Frame|];split;[exact Forward|eapply schnorr_startup_framed;[exact Ready|exact Forward|exact Frame]].
Qed.
