(** Strict field parsing before original x-only key decompression. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_word_repr C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_set_b32_owned
 C.jet_secp_multiply_normalize_bridge C.jet_secp_swu_raw_input C.jet_secp_generator_codec
 C.jet_secp_input_bytes C.jet_secp_output_bytes C.jet_secp_root_chain_owned
 C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_decode C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition xonly_input_bytes (pk:Ty.tySem (Word 8)):=be_bytes (@toZ (WordToZ 8) pk).
Lemma xonly_input_length pk:length (xonly_input_bytes pk)=32%nat.
Proof. unfold xonly_input_bytes,be_bytes;rewrite map_length,seq_length;reflexivity. Qed.
Lemma xonly_input_bounds pk:Forall (fun x=>0<=x<=255) (xonly_input_bytes pk).
Proof.
 unfold xonly_input_bytes;rewrite <-be_chunks_32.
 eapply Forall_impl;[|apply be_chunks_byte_bounds];intros x Bounds;change (0<=x<256) in Bounds;lia.
Qed.
Lemma xonly_input_value pk:be_val (xonly_input_bytes pk)=@toZ (WordToZ 8) pk.
Proof. apply generator_be_bytes_value;apply word_toZ_range. Qed.
Definition xonly_strict_flag (pk:Ty.tySem (Word 8)):=if Z.ltb (@toZ (WordToZ 8) pk) feP then Int.one else Int.zero.
Definition xonly_parse_result pk:=if Z.ltb (@toZ (WordToZ 8) pk) feP then xonly_decode_result pk else Int.zero.
Definition xonly_parsed_result pk m b:=@toZ (WordToZ 8) pk<feP ->xonly_saved_result pk m b.
Definition xonly_parse_field_call:=curve_call _secp256k1_fe_set_b32 f_secp256k1_fe_set_b32 (Some _t'1)
 [xonly_parse_x_address;Etempvar _input32 (tptr tuchar)].
Definition xonly_parse_field_return:=Ssequence
 (Ssequence xonly_parse_field_call (xonly_parse_guard _t'1)) xonly_parse_decode_return.
Lemma xonly_parse_field_return_source:
 root_drop_statements 3 (fn_body f_secp256k1_xonly_pubkey_parse)=xonly_parse_field_return.
Proof. reflexivity. Qed.
Theorem eval_xonly_field_read pk m bx bin:
 bx<>bin ->Mem.range_perm m bx 0 40 Cur Freeable ->Mem.range_perm m bin 0 32 Cur Freeable ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
 [Vptr bx Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint (xonly_strict_flag pk)) /\
 fe_at mf bx 0 (words5 (swu_raw_words pk)) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\Mem.range_perm mf bin 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bx /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros Sep FreeX FreeIn Input.
 assert (Loads:forall i,(i<32)%nat ->Mem.load Mint8unsigned m bin (Z.of_nat i)=
  Some (Vint (Int.repr (nth i (xonly_input_bytes pk) 0)))).
 { intros i Bound;apply Input;rewrite nth_error_map,(nth_error_nth' _ 0);[reflexivity|rewrite xonly_input_length;exact Bound]. }
 destruct (eval_set_b32_owned (xonly_input_bytes pk) m bx bin
  (xonly_input_length pk) (xonly_input_bounds pk) Sep FreeX FreeIn Loads)
 as (mf & Call & Field & FreeXF & FreeInF & BytesF & Frame & Read).
 rewrite xonly_input_value in Call,Field.
 exists mf;split.
 - unfold xonly_strict_flag;destruct (Z.ltb (@toZ (WordToZ 8) pk) feP);exact Call.
 - split;[exact Field|];split;[exact FreeXF|];split;[exact FreeInF|];split;assumption.
Qed.
Theorem exec_xonly_parse_field (Model:memcpy_model) pk e le m bp bx bout bin:
 e!_pk=Some (bp,curve_ge_type) ->e!_x=Some (bx,curve_fe_type) ->
 e!_secp256k1_fe_set_b32=None ->e!_secp256k1_ge_set_xo_var=None ->
 e!_secp256k1_ge_is_in_correct_subgroup=None ->e!_secp256k1_xonly_pubkey_save=None ->
 le!_pubkey=Some (Vptr bout Ptrofs.zero) ->le!_input32=Some (Vptr bin Ptrofs.zero) ->
 NoDup [bp;bx;bout;bin] ->
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf lef,
 Clight2.exec_stmt secp_ge e le m xonly_parse_field_return E0 lef mf
 (Out_return (Some (Vint (xonly_parse_result pk),tint))) /\
 xonly_parsed_result pk mf bout /\
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bx /\b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros P X ReadSym DecodeSym SubgroupSym SaveSym Key InputPtr Separate Owned Input.
 assert (Pairs:bp<>bx /\bp<>bout /\bp<>bin /\bx<>bout /\bx<>bin /\bout<>bin).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct Pairs as (PX & PO & PI & XO & XI & OI).
 destruct (eval_xonly_field_read pk m bx bin XI
  (Owned bx 40 ltac:(clear;cbn [In];tauto)) (Owned bin 32 ltac:(clear;cbn [In];tauto)) Input)
 as (mr & Read & Field & FreeX & FreeIn & FrameR & ReadR).
 assert (OwnedR:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mr b 0 hi Cur Freeable).
 { intros b hi [Same|[Same|[Same|[Same|[]]]]];inversion Same;subst b hi.
   - eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameR|intros;split;assumption].
   - exact FreeX.
   - eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameR|intros;split;congruence].
   - exact FreeIn. }
 pose (lr:=PTree.set _t'1 (Vint (xonly_strict_flag pk)) le).
 assert (ReadStmt:Clight2.exec_stmt secp_ge e le m xonly_parse_field_call E0 lr mr Out_normal).
 { unfold xonly_parse_field_call,lr;eapply exec_curve_call with (vargs:=[Vptr bx Ptrofs.zero;Vptr bin Ptrofs.zero])
   (v:=Vint (xonly_strict_flag pk)).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact ReadSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact X|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact InputPtr|reflexivity|constructor].
   - exact Read. }
 destruct (Z.ltb (@toZ (WordToZ 8) pk) feP) eqn:Accepted.
 - assert (Flag:xonly_strict_flag pk=Int.one) by (unfold xonly_strict_flag;rewrite Accepted;reflexivity).
   destruct (exec_xonly_parse_decode Model (swu_raw_words pk) pk e lr mr bp bx bout
    P X DecodeSym SubgroupSym SaveSym
    ltac:(unfold lr;rewrite PTree.gso by discriminate;exact Key)
    ltac:(clear -PX PO XO;repeat constructor;cbn [In];intuition congruence)
    (swu_raw_matches pk) Field ltac:(intros b hi Slot;apply OwnedR;clear -Slot;cbn [In] in *;tauto))
   as (mf & lef & Decode & Saved & OwnedD & FrameD & ReadD).
   exists mf,lef;split.
   + unfold xonly_parse_result;rewrite Accepted.
     unfold xonly_parse_field_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=lr);[|exact Decode].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=lr);[exact ReadStmt|].
     apply exec_xonly_guard_one;unfold lr;rewrite Flag;apply PTree.gss.
   + split;[intros _;exact Saved|];split.
     * intros b hi [Same|[Same|[Same|[Same|[]]]]];inversion Same;subst b hi.
       -- apply OwnedD;clear;cbn [In];tauto.
       -- apply OwnedD;clear;cbn [In];tauto.
       -- apply OwnedD;clear;cbn [In];tauto.
       -- eapply curve_keep_free;[lia|exact FreeIn|exact FrameD|intros;repeat split;congruence].
     * split.
       -- eapply lframe_trans.
          { eapply lframe_implies;[exact FrameR|];intros b pos (_ & NX & _ & NI) _;split;assumption. }
          { eapply lframe_implies;[exact FrameD|];intros b pos (NP & NX & NO & _) _;repeat split;assumption. }
       -- eapply preserved_trans;[exact ReadR|exact ReadD].
 - assert (Flag:xonly_strict_flag pk=Int.zero) by (unfold xonly_strict_flag;rewrite Accepted;reflexivity).
   exists mr,lr;split.
   + unfold xonly_parse_result;rewrite Accepted.
     unfold xonly_parse_field_return;eapply exec_Sseq_2 with (t1:=E0);[|discriminate].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=lr);[exact ReadStmt|].
     apply exec_xonly_guard_zero;unfold lr;rewrite Flag;apply PTree.gss.
   + split.
     * intros Bound;apply Z.ltb_ge in Accepted;exfalso;lia.
     * split;[exact OwnedR|];split;[|exact ReadR].
       eapply lframe_implies;[exact FrameR|];intros b pos (_ & NX & _ & NI) _;split;assumption.
Qed.
