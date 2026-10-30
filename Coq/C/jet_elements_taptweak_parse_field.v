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
Require Import C.jet_secp_xonly_parse_field C.jet_elements_taptweak_set_b32
 C.jet_elements_taptweak_pure C.jet_elements_taptweak_parse_start.
Require Import C.jet_elements_taptweak_parse_decode.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque elements_taptweak_ge.
Theorem exec_elements_taptweak_parse_field (Model:memcpy_model) pk e le m bp bx bout bin:
 e!_pk=Some (bp,curve_ge_type) ->e!_x=Some (bx,curve_fe_type) ->
 e!_secp256k1_fe_set_b32=None ->e!_secp256k1_ge_set_xo_var=None ->
 e!_secp256k1_ge_is_in_correct_subgroup=None ->e!_secp256k1_xonly_pubkey_save=None ->
 le!_pubkey=Some (Vptr bout Ptrofs.zero) ->le!_input32=Some (Vptr bin Ptrofs.zero) ->
 NoDup [bp;bx;bout;bin] ->
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf lef,
 Clight2.exec_stmt elements_taptweak_ge e le m xonly_parse_field_return E0 lef mf
 (Out_return (Some (Vint (xonly_parse_result pk),tint))) /\
 xonly_parsed_result pk mf bout /\
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bx /\b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros P X ReadSym DecodeSym SubgroupSym SaveSym Key InputPtr Separate Owned Input.
 assert (Pairs:bp<>bx /\bp<>bout /\bp<>bin /\bx<>bout /\bx<>bin /\bout<>bin).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct Pairs as (PX & PO & PI & XO & XI & OI).
 destruct (eval_elements_taptweak_xonly_field_read pk m bx bin XI
  (Owned bx 40 ltac:(clear;cbn [In];tauto)) (Owned bin 32 ltac:(clear;cbn [In];tauto)) Input)
 as (mr & Read & Field & FreeX & FreeIn & FrameR & ReadR).
 assert (OwnedR:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mr b 0 hi Cur Freeable).
 { intros b hi [Same|[Same|[Same|[Same|[]]]]];inversion Same;subst b hi.
   - eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameR|intros;split;assumption].
   - exact FreeX.
   - eapply curve_keep_free;[lia|apply Owned;clear;cbn [In];tauto|exact FrameR|intros;split;congruence].
   - exact FreeIn. }
 pose (lr:=PTree.set _t'1 (Vint (xonly_strict_flag pk)) le).
 assert (ReadStmt:Clight2.exec_stmt elements_taptweak_ge e le m xonly_parse_field_call E0 lr mr Out_normal).
 { unfold xonly_parse_field_call,lr;eapply exec_elements_taptweak_parse_call with (vargs:=[Vptr bx Ptrofs.zero;Vptr bin Ptrofs.zero])
   (v:=Vint (xonly_strict_flag pk)).
   - unfold elements_taptweak_parse_helpers;repeat first [left;reflexivity|right].
   - exact ReadSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact X|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact InputPtr|reflexivity|constructor].
   - exact Read. }
 destruct (Z.ltb (@toZ (WordToZ 8) pk) feP) eqn:Accepted.
 - assert (Flag:xonly_strict_flag pk=Int.one) by (unfold xonly_strict_flag;rewrite Accepted;reflexivity).
   destruct (exec_elements_taptweak_parse_decode Model (swu_raw_words pk) pk e lr mr bp bx bout
    P X DecodeSym SubgroupSym SaveSym
    ltac:(unfold lr;rewrite PTree.gso by discriminate;exact Key)
    ltac:(clear -PX PO XO;repeat constructor;cbn [In];intuition congruence)
    (swu_raw_matches pk) Field ltac:(intros b hi Slot;apply OwnedR;clear -Slot;cbn [In] in *;tauto))
   as (mf & lef & Decode & Saved & OwnedD & FrameD & ReadD).
   exists mf,lef;split.
   + unfold xonly_parse_result;rewrite Accepted.
     unfold xonly_parse_field_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=lr);[|exact Decode].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=lr);[exact ReadStmt|].
     apply exec_elements_taptweak_xonly_guard_one;unfold lr;rewrite Flag;apply PTree.gss.
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
     apply exec_elements_taptweak_xonly_guard_zero;unfold lr;rewrite Flag;apply PTree.gss.
   + split.
     * intros Bound;apply Z.ltb_ge in Accepted;exfalso;lia.
     * split;[exact OwnedR|];split;[|exact ReadR].
       eapply lframe_implies;[exact FrameR|];intros b pos (_ & NX & _ & NI) _;split;assumption.
Qed.
