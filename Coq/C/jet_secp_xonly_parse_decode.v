(** Both decompression outcomes of the original x-only public-key parser. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_secp_root_chain_numeric C.jet_secp_decompress_helper_literal C.jet_secp_decompress_literal
 C.jet_secp_decompress_output C.jet_secp_decompress_native_save C.jet_secp_closed_helpers
 C.jet_clight_internal_frame C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require Import C.jet_secp_xonly_parse_control.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress.
Lemma xonly_decode_allowed:allowed_call secp_closed_helpers (Internal f_secp256k1_ge_set_xo_var).
Proof. exists _secp256k1_ge_set_xo_var,f_secp256k1_ge_set_xo_var;split;vm_compute;reflexivity. Qed.
Theorem exec_xonly_parse_decode (Model:memcpy_model) w (pk:Ty.tySem (Word 8)) e le m bp bx bout:
 e!_pk=Some (bp,curve_ge_type) ->e!_x=Some (bx,curve_fe_type) ->
 e!_secp256k1_ge_set_xo_var=None ->e!_secp256k1_ge_is_in_correct_subgroup=None ->
 e!_secp256k1_xonly_pubkey_save=None ->le!_pubkey=Some (Vptr bout Ptrofs.zero) ->
 NoDup [bp;bx;bout] ->root_words_match w pk ->fe_at m bx 0 (words5 w) ->
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m xonly_parse_decode_return E0 lef mf
 (Out_return (Some (Vint (xonly_decode_result pk),tint))) /\
 xonly_saved_result pk mf bout /\
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bx /\b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros P X DecodeSym SubgroupSym SaveSym Key Separate Match Input Owned.
 assert (Pairs:bx<>bp /\bp<>bout /\bx<>bout).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 destruct Pairs as (XP & PO & XO).
 destruct (eval_decompress_helper_literal w pk (inl tt) m bx bp XP Match Input
  (Owned bx 40 ltac:(clear;cbn [In];tauto)) (Owned bp 88 ltac:(clear;cbn [In];tauto)))
 as (md & Decode & FieldX & FieldY & BoundX & BoundY & Flag & Machine & FreeX & FreeP & FrameD).
 pose proof (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
  _ _ _ _ _ _ Decode xonly_decode_allowed) as KeepD.
 pose proof (proj2 (internal_exec_preserved _ _ secp_closed_helpers_ok)
  _ _ _ _ _ _ Decode xonly_decode_allowed) as ReadD.
 assert (OwnedD:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64)] ->Mem.range_perm md b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepD;exact (Owned b hi Slot pos Range). }
 assert (DecodeStmt:Clight2.exec_stmt secp_ge e le m xonly_parse_decode E0
  (PTree.set _t'2 (Vint (xonly_decode_result pk)) le) md Out_normal).
 { unfold xonly_parse_decode;eapply exec_curve_call with
   (vargs:=[Vptr bp Ptrofs.zero;Vptr bx Ptrofs.zero;Vint Int.zero]) (v:=Vint (xonly_decode_result pk)).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - exact DecodeSym.
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact P|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact X|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|constructor].
   - exact Decode. }
 destruct (@literal_decompress Simplicity.Alg.CoreFunSem ((inl tt),pk)) as [u|[ax ay]] eqn:Literal.
 - assert (Result:xonly_decode_result pk=Int.zero) by (unfold xonly_decode_result;rewrite Literal;reflexivity).
   rewrite Result in DecodeStmt;rewrite Result;exists md,(PTree.set _t'2 (Vint Int.zero) le);split.
   + unfold xonly_parse_decode_return;eapply exec_Sseq_2 with (t1:=E0);[|discriminate].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=PTree.set _t'2 (Vint Int.zero) le);[exact DecodeStmt|].
     apply exec_xonly_guard_zero;apply PTree.gss.
   + split.
     * intros a b Impossible;rewrite Literal in Impossible;discriminate.
     * split;[exact OwnedD|];split;[|exact ReadD].
       eapply lframe_implies;[exact FrameD|];intros b pos (NP & NX & _) _;split;assumption.
 - assert (Result:xonly_decode_result pk=Int.one) by (unfold xonly_decode_result;rewrite Literal;reflexivity).
   rewrite Result in DecodeStmt;rewrite Result.
   destruct (eval_decompressed_native_save Model w pk (inl tt) ax ay md bp bout Match Literal
    FieldX FieldY (OwnedD bout 64 ltac:(clear;cbn [In];tauto)))
   as (mf & storage & Save & Storage & ValueX & ValueY & FreeOut & FrameS & ReadS).
   pose (ld:=PTree.set _t'2 (Vint Int.one) le).
   pose (ls:=PTree.set _t'3 (Vint Int.one) ld).
   assert (Subgroup:Clight2.exec_stmt secp_ge e ld md xonly_parse_subgroup E0 ls md Out_normal).
   { unfold xonly_parse_subgroup,ls;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vint Int.one).
     - unfold secp_pure;repeat first [left;reflexivity|right].
     - exact SubgroupSym.
     - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact P|reflexivity|constructor].
     - apply eval_xonly_correct_subgroup. }
   assert (SaveStmt:Clight2.exec_stmt secp_ge e ls md xonly_parse_save E0 ls mf Out_normal).
   { unfold xonly_parse_save;eapply exec_curve_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bp Ptrofs.zero]) (v:=Vundef).
     - unfold secp_pure;repeat first [left;reflexivity|right].
     - exact SaveSym.
     - eapply eval_Econs.
       + apply eval_Etempvar;unfold ls,ld;rewrite !PTree.gso by discriminate;exact Key.
       + reflexivity.
       + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact P|reflexivity|constructor].
     - exact Save. }
   exists mf,ls;split.
   + unfold xonly_parse_decode_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=ld).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=ld);[exact DecodeStmt|].
       apply exec_xonly_guard_one;unfold ld;apply PTree.gss.
     * unfold xonly_parse_after_decode;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=ls).
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=ls);[exact Subgroup|].
          apply exec_xonly_guard_one;unfold ls;apply PTree.gss.
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=ls);[exact SaveStmt|].
          apply exec_Sreturn_some;constructor.
   + split.
     * intros a b DecodePair;rewrite Literal in DecodePair;injection DecodePair as <- <-.
       exists storage;split;[exact Storage|];split;assumption.
     * split.
       { intros b hi Slot;destruct (Pos.eq_dec b bout) as [Same|Other].
         - subst b;assert (Size:hi=64) by (clear -Slot Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence).
           subst hi;exact FreeOut.
         - eapply curve_keep_free;[|apply OwnedD;exact Slot|exact FrameS|intros;exact Other].
           clear -Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia. }
       split.
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameD|];intros b pos (NP & NX & _) _;split;assumption.
         - eapply lframe_implies;[exact FrameS|];intros b pos (_ & _ & NO) _;exact NO. }
       { eapply preserved_trans;[exact ReadD|exact ReadS]. }
Qed.
