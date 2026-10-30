(** Actual linked 17-byte tag hash and output-prefix composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Digest.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_memcpy_model C.jet_uint32_array_init
 C.jet_secp_taptweak_entry C.jet_secp_taptweak_tag C.jet_secp_taptweak_tag_exec C.jet_secp_taptweak_prefix
 C.jet_secp_curve_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_taptweak_body_prefix C.jet_elements_taptweak_pure C.jet_elements_taptweak_tag
 C.jet_elements_taptweak_tag_runtime C.jet_elements_taptweak_tag_state_at.
Require Import C.jet_elements_taptweak_runtime_ready C.jet_elements_taptweak_output_prefix.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_runtime_tag_block.
Local Ltac distinct Sep:=clear -Sep;unfold taptweak_locals in Sep;
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_elements_taptweak_initial_phase (Copy:memcpy_model) le m bb bi bo bp bt bh bs bc bc1 br br1:
 le!_tagName__3=Some (Vptr elements_taptweak_runtime_tag_block Ptrofs.zero) ->le!_tagLen=Some (Vlong (Int64.repr 17)) ->
 NoDup (taptweak_locals bb bi bo bp bt bh bs bc bc1 br br1) ->
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 elements_taptweak_runtime_ready m ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) le m taptweak_initial_phase E0 le mf Out_normal /\
 uint32_array_at mf bt 0 (Digest.hash256_reg elements_taptweak_tag_digest) /\
 uint32_array_at mf bs 0 (Digest.hash256_reg elements_taptweak_tag_iv) /\
 Mem.load Mptr mf bc1 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc1 8=Some (Vlong (Int64.repr 64)) /\Mem.load Mint8unsigned mf bc1 80=Some (Vint Int.zero) /\
 (forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>br1 /\b<>bc /\b<>bt /\b<>br /\b<>bc1 /\b<>bs) m mf /\
 readonly_preserved m mf /\elements_taptweak_runtime_ready mf.
Proof.
 intros Name Len Sep Owned Startup.
 assert (TagSep:NoDup [br1;bc;bt]).
 { clear -Sep;unfold taptweak_locals in Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;
 repeat constructor;cbn [In];intuition congruence. }
 assert(TagGlobal:elements_taptweak_tag_state_at elements_taptweak_runtime_tag_block m)by exact(proj1(proj2(proj2 Startup))).
 assert(TagApart:forall b hi,In(b,hi)(taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->0<hi ->b<>elements_taptweak_runtime_tag_block).
 { intros b hi Member Positive;eapply elements_taptweak_tag_owned_separate_at;[exact TagGlobal|exact Positive|apply Owned;exact Member]. }
 destruct(exec_elements_taptweak_tag Copy(taptweak_env bb bi bo bp bt bh bs bc bc1 br br1)le m br1 bc bt elements_taptweak_runtime_tag_block
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Name Len TagSep
 ltac:(intro Same;apply(TagApart br1 88 ltac:(clear;cbn[taptweak_storage In];tauto) ltac:(lia));symmetry;exact Same)
 ltac:(intro Same;apply(TagApart bc 88 ltac:(clear;cbn[taptweak_storage In];tauto) ltac:(lia));symmetry;exact Same)
 ltac:(intro Same;apply(TagApart bt 32 ltac:(clear;cbn[taptweak_storage In];tauto) ltac:(lia));symmetry;exact Same)
 (proj1(proj2 Startup))(proj1 TagGlobal)
 (Owned br1 88 ltac:(clear;cbn[taptweak_storage In];tauto))
 (Owned bc 88 ltac:(clear;cbn[taptweak_storage In];tauto))
 (Owned bt 32 ltac:(clear;cbn[taptweak_storage In];tauto)))as
 (mt & Tag & TagHash & TagPointer & TagCounter & TagOverflow & FRT & FCT & FTT & FrameT & ReadT & SHAT & BytesT).
 assert(StartupT:elements_taptweak_runtime_ready mt).
 { eapply elements_taptweak_runtime_ready_owned with(slots:=[(br1,88);(bc,88);(bt,32)]);
   [exact Startup|exact ReadT| |].
   - intros b hi[Same|[Same|[Same|[]]]];injection Same as <- <-;(split;[lia|apply Owned;clear;cbn[taptweak_storage In];tauto]).
   - eapply lframe_implies;[exact FrameT|intros b pos Outside Valid;clear -Outside;cbn[map fst In]in Outside|-*;intuition congruence]. }
 assert (OwnedT:forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mt b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [taptweak_storage In] in Slot;
 repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
 match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
 try assumption.
 all:eapply curve_keep_free;[clear;lia|apply Owned;clear;cbn [taptweak_storage In];tauto|exact FrameT|intros;repeat split;distinct Sep]. }
 assert (PrefixSep:NoDup [br;bc1;bs;bt]).
 { clear -Sep;unfold taptweak_locals in Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;
 repeat constructor;cbn [In];intuition congruence. }
 destruct (exec_elements_taptweak_output_prefix Copy (taptweak_env bb bi bo bp bt bh bs bc bc1 br br1) le mt br bc1 bs bt
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl PrefixSep StartupT
 (OwnedT br 88 ltac:(clear;cbn [taptweak_storage In];tauto))
 (OwnedT bc1 88 ltac:(clear;cbn [taptweak_storage In];tauto))
 (OwnedT bs 32 ltac:(clear;cbn [taptweak_storage In];tauto))
 (OwnedT bt 32 ltac:(clear;cbn [taptweak_storage In];tauto)) TagHash) as
 (mf & Prefix & StateF & PointerF & CounterF & OverflowF & FRF & FCF & FSF & FTF & TagHashF & FrameF & ReadF & StartupF).
 assert (OwnedF:forall b hi,In (b,hi) (taptweak_storage bb bi bo bp bt bh bs bc bc1 br br1) ->Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Slot;cbn [taptweak_storage In] in Slot;
 repeat match goal with S:_ \/ _ |- _=>destruct S as [S|S] end;try contradiction;
 match goal with S:(_,_) = (_,_) |- _=>inversion S;subst b hi end;
 try assumption.
 all:eapply curve_keep_free;[clear;lia|apply OwnedT;clear;cbn [taptweak_storage In];tauto|exact FrameF|intros;repeat split;distinct Sep]. }
 exists mf;split.
 - unfold taptweak_initial_phase;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt);[exact Tag|exact Prefix].
 - split;[exact TagHashF|];split;[exact StateF|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
 split;[exact OwnedF|];split.
   + eapply lframe_trans;
     [eapply lframe_implies;[exact FrameT|intros b pos (R1 & C & T & R & C1 & S) Valid;repeat split;assumption]|
      eapply lframe_implies;[exact FrameF|intros b pos (R1 & C & T & R & C1 & S) Valid;repeat split;assumption]].
   + split;[eapply preserved_trans;[exact ReadT|exact ReadF]|exact StartupF].
Qed.
