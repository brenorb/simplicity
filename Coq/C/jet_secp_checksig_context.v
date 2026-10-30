(** Original CheckSig constructor call and actual context assignment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements
 C.jet_secp_checksig_tag C.jet_secp_checksig_tagged C.jet_secp_context_copy
 C.jet_secp_root_chain_owned C.jet_secp_schnorr_challenge_entry C.jet_secp_generator_sha_start C.jet_secp_local_regions
 C.jet_memcpy_model C.jet_sha_ctx8_model C.jet_uint32_array_init C.jet_sx_mem
 C.jet_clight_internal_preserve C.jet_secp_schnorr_challenge_owned.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition checksig_output_expr:=Efield (Evar _output (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8).
Definition checksig_tag_call:=curve_call _sha256_tagged_init f_sha256_tagged_init None
 [Eaddrof (Evar __res (Tstruct _sha256_context noattr)) (tptr (Tstruct _sha256_context noattr));
  checksig_output_expr;
  Eaddrof (Evar _signatureIV (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr))].
Definition checksig_context_setup:=Ssequence checksig_tag_call (sha_context_copy _ctx __res).
Lemma checksig_context_source:
 match root_drop_statements 3 (fn_body f_simplicity_check_sig_verify) with
 | Ssequence (Ssequence setup _) _=>setup|_=>Sskip end=checksig_context_setup.
Proof. reflexivity. Qed.
Lemma checksig_tagged_symbols:
 Genv.find_symbol secp_ge _sha256_tagged_init=Some (secp_symbol_block _sha256_tagged_init) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _sha256_tagged_init) Ptrofs.zero)=Some (Internal f_sha256_tagged_init).
Proof. vm_compute;split;reflexivity. Qed.
Local Opaque secp_ge checksig_tag_block.
Lemma eval_checksig_output e le m bs:e!_output=Some (bs,Tstruct _sha256_midstate noattr) ->
 eval_expr secp_ge e le m checksig_output_expr (Vptr bs Ptrofs.zero).
Proof.
 intro Output;destruct generator_sha_state_layout as (co & Layout & Offset).
 unfold checksig_output_expr;eapply eval_Elvalue with (loc:=bs) (ofs:=Ptrofs.zero) (bf:=Full).
 - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Output|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Layout.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Lemma exec_checksig_tag_call e le m mf br bs:
 e!__res=Some (br,Tstruct _sha256_context noattr) ->e!_output=Some (bs,Tstruct _sha256_midstate noattr) ->
 e!_signatureIV=None ->e!_sha256_tagged_init=None ->
 Clight2.eval_funcall secp_ge m (Internal f_sha256_tagged_init)
 [Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr checksig_tag_block Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m checksig_tag_call E0 le mf Out_normal.
Proof.
 intros Result Output GlobalTag GlobalFun Call;destruct checksig_tagged_symbols as [Symbol Function].
 unfold checksig_tag_call,curve_call;eapply exec_Scall with
 (vf:=Vptr (secp_symbol_block _sha256_tagged_init) Ptrofs.zero) (f:=Internal f_sha256_tagged_init)
 (vargs:=[Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr checksig_tag_block Ptrofs.zero]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[apply eval_Evar_global;[exact GlobalFun|exact Symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Result|reflexivity|].
   eapply eval_Econs;[apply eval_checksig_output;exact Output|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_global;[exact GlobalTag|exact checksig_tag_symbol]|reflexivity|constructor].
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Theorem exec_checksig_context_setup (Model:memcpy_model) e le m bc br bs:
 e!_ctx=Some (bc,Tstruct _sha256_context noattr) ->e!__res=Some (br,Tstruct _sha256_context noattr) ->
 e!_output=Some (bs,Tstruct _sha256_midstate noattr) ->e!_signatureIV=None ->e!_sha256_tagged_init=None ->
 NoDup [bc;br;bs] ->checksig_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m checksig_context_setup E0 le mf Out_normal /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 uint32_array_at mf bs 0 (state_regs checksig_iv_word) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>br /\b<>bs) m mf /\readonly_preserved m mf /\checksig_startup mf.
Proof.
 intros Context Result Output GlobalTag GlobalFun Separate Ready FC FR FS.
 assert (CB:bc<>br /\bc<>bs /\br<>bs).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 destruct CB as [CR [CS RS]].
 destruct (eval_checksig_tagged_init Model m br bs RS Ready FR FS)
 as (mt & Tag & PointerT & CounterT & OverflowT & StateT & FRT & FST & FrameT & ReadT & ReadyT).
 assert (FCT:Mem.range_perm mt bc 0 88 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameT|intros;split;assumption|exact FC]. }
 destruct (exec_sha_context_copy _ctx __res e le mt bc br (Vptr bs Ptrofs.zero)
  (Int64.repr 64) Int.zero Context Result CR FCT FRT PointerT CounterT OverflowT)
 as (mf & Copy & PointerF & CounterF & OverflowF & FCF & FRF & FrameF & ReadF).
 assert (FSF:Mem.range_perm mf bs 0 32 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameF|intros;congruence|exact FST]. }
 exists mf;split.
 - unfold checksig_context_setup;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mt).
   + eapply exec_checksig_tag_call;[exact Result|exact Output|exact GlobalTag|exact GlobalFun|exact Tag].
   + exact Copy.
 - split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];split.
   + intros i v Nth;rewrite (proj1 FrameF).
     * exact (StateT i v Nth).
     * eapply Mem.perm_valid_block;apply (FST 0);lia.
     * intros;congruence.
   + split;[exact FCF|];split;[exact FRF|];split;[exact FSF|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameT|intros b pos [C [R S]] Old;split;assumption].
       -- eapply lframe_implies;[exact FrameF|intros b pos [C [R S]] Old;exact C].
     * split;[eapply preserved_trans;[exact ReadT|exact ReadF]|].
       eapply checksig_startup_owned_forward with (slots:=[(bc,88)]);
        [exact ReadyT|exact (proj1 ReadF)| |].
       -- intros b hi Slot;destruct Slot as [Slot|Empty];[inversion Slot;subst;split;[lia|exact FCT]|contradiction].
       -- eapply lframe_implies;[exact FrameF|];intros b pos Outside Old;cbn [map fst In] in Outside;intuition congruence.
Qed.
