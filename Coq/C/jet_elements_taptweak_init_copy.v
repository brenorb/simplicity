(** Original SHA initialization and normalized struct-copy at arbitrary local identifiers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_mem C.jet_uint32_array_init
 C.jet_sha256_iv_init C.jet_secp_sha_owned C.jet_secp_context_copy
 C.jet_secp_generator_sha_start C.jet_secp_sha_pure_transport C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_clight_forward C.jet_clight_internal_preserve
 C.jet_elements_taptweak_pure C.jet_secp_sha_init_copy C.jet_secp_schnorr_challenge_entry C.jet_transport.
Require C.jets_sha.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_sha_context_copy_at.
Lemma elements_taptweak_sha_context_size:
 sizeof (genv_cenv elements_taptweak_ge) schnorr_challenge_context_type=88.
Proof. vm_compute;reflexivity. Qed.
Definition exec_elements_taptweak_sha_context_copy:=exec_sha_context_copy_at
 elements_taptweak_ge elements_taptweak_sha_context_size.
Lemma elements_taptweak_sha_state_members:
 option_map co_members ((genv_cenv elements_taptweak_ge)!_sha256_midstate)=
 Some [Member_plain _s (tarray tuint 8)].
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.
Lemma elements_taptweak_sha_state_layout:
 exists co,(genv_cenv elements_taptweak_ge)!_sha256_midstate=Some co /\
 field_offset (genv_cenv elements_taptweak_ge) _s (co_members co)=Errors.OK (0,Full).
Proof.
 pose proof elements_taptweak_sha_state_members as Members.
 destruct ((genv_cenv elements_taptweak_ge)!_sha256_midstate) as [co|] eqn:Cenv;[|discriminate].
 exists co;split;[reflexivity|].
 inversion Members as [Fields];rewrite Fields;reflexivity.
Qed.
Local Opaque elements_taptweak_ge.
Lemma eval_elements_taptweak_sha_local_state sid e le m bs:e!sid=Some (bs,generator_sha_state_type) ->
 eval_expr elements_taptweak_ge e le m (Efield (Evar sid generator_sha_state_type) _s (tarray tuint 8)) (Vptr bs Ptrofs.zero).
Proof.
 intro State;destruct elements_taptweak_sha_state_layout as (co & Cenv & Offset).
 eapply eval_Elvalue with (loc:=bs) (ofs:=Ptrofs.zero) (bf:=Full).
 - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact State|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Cenv.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Theorem exec_elements_taptweak_sha_init_copy rid cid sid e le m br bc bs:
 e!_sha256_init=None ->e!rid=Some (br,generator_sha_ctx_type) ->
 e!cid=Some (bc,generator_sha_ctx_type) ->e!sid=Some (bs,generator_sha_state_type) ->
 NoDup [br;bc;bs] ->Mem.range_perm m br 0 88 Cur Freeable ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m (sha_init_copy_stmt rid cid sid) E0 le mf Out_normal /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong Int64.zero) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 uint32_array_at mf bs 0 sha256_iv_words /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros Global Result Context State Sep FR FC FS.
 assert (RS:br<>bs) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 assert (CS:bc<>bs) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 assert (CR:bc<>br) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 destruct (eval_elements_taptweak_sha_init_owned m br bs RS FR FS) as
 (mi & Init & Pointer & Counter & Overflow & IV & FRI & FSI & FrameI & ReadI).
 assert (FCI:Mem.range_perm mi bc 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FC|exact FrameI|intros;split;congruence]. }
 destruct (exec_elements_taptweak_sha_context_copy cid rid e le mi bc br (Vptr bs Ptrofs.zero) Int64.zero Int.zero
 Context Result CR FCI FRI Pointer Counter Overflow) as
 (mf & Copy & PointerF & CounterF & OverflowF & FCF & FRF & FrameC & ReadC).
 assert (VS:Mem.valid_block mi bs) by (eapply Mem.perm_valid_block;apply (FSI 0);clear;lia).
 exists mf;split.
 - unfold sha_init_copy_stmt;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi);[|exact Copy].
   destruct (elements_taptweak_sha_pure_entries C.jets_sha._sha256_init C.jets_sha.f_sha256_init
     ltac:(right;left;reflexivity)) as (b1 & b2 & S1 & F1 & S2 & F2).
   unfold sha_init_copy_call,curve_call;eapply exec_Scall with (vf:=Vptr b2 Ptrofs.zero)
     (f:=Internal f_sha256_init) (vargs:=[Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero]) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact S2]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Result|reflexivity|].
     eapply eval_Econs;[apply eval_elements_taptweak_sha_local_state;exact State|reflexivity|constructor].
   + exact F2.
   + reflexivity.
   + exact Init.
 - split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];split.
   + intros i x Nth;rewrite (proj1 FrameC Mint32 bs (0+4*Z.of_nat i) VS);[apply IV;exact Nth|intros;congruence].
   + split;[exact FRF|];split;[exact FCF|];split.
     * eapply curve_keep_free;[clear;lia|exact FSI|exact FrameC|intros;congruence].
     * split.
       -- eapply lframe_trans;
          [eapply lframe_implies;[exact FrameI|intros b pos [NR [NC NS]] Valid;split;assumption]|
           eapply lframe_implies;[exact FrameC|intros b pos [NR [NC NS]] Valid;exact NC]].
       -- eapply preserved_trans;[exact ReadI|exact ReadC].
Qed.
