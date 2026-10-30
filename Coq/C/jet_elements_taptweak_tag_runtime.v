(** The original generic TapTweak tag-hashing block for every short caller tag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require sha.SHA256.
Require Import C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_mem C.jet_frame_inv C.jet_read8s_layout
 C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha_ctx8_model C.jet_sha_finalize_exec C.jet_sha_be32_write
 C.jet_memcpy_model C.jet_secp_sha_startup C.jet_secp_sha_init_copy C.jet_secp_sha_absorb_short
 C.jet_secp_sha_finalize_short C.jet_secp_schnorr_challenge_body C.jet_secp_taptweak_tag_exec
 C.jet_secp_curve_frame C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals
 C.jet_elements_taptweak_absorb_short C.jet_elements_taptweak_finalize_short C.jet_secp_taptweak_tag_runtime C.jet_secp_curve_statements.
Require Import C.jet_elements_taptweak_init_copy.
From compcert Require Import Globalenvs.
Definition elements_taptweak_sha_call_functions:=
 [(_sha256_uchars,f_sha256_uchars);(_sha256_finalize,f_sha256_finalize)].
Lemma elements_taptweak_sha_call_symbols id fd:In (id,fd) elements_taptweak_sha_call_functions ->
 Genv.find_symbol elements_taptweak_ge id=Some (elements_taptweak_symbol_block id) /\
 Genv.find_funct elements_taptweak_ge (Vptr (elements_taptweak_symbol_block id) Ptrofs.zero)=Some (Internal fd).
Proof.
 intros [Pair|[Pair|[]]];inversion Pair;subst;vm_compute;split;reflexivity.
Qed.
Local Opaque elements_taptweak_ge.
Lemma exec_elements_taptweak_sha_call id fd args vargs v e le m mf:
 In (id,fd) elements_taptweak_sha_call_functions ->e!id=None ->
 eval_exprlist elements_taptweak_ge e le m args (type_of_params (fn_params fd)) vargs ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal fd) vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m (curve_call id fd None args) E0 le mf Out_normal.
Proof.
 intros Member Global Args Call;destruct (elements_taptweak_sha_call_symbols id fd Member) as [Symbol Function].
 unfold curve_call;eapply exec_Scall with (vf:=Vptr (elements_taptweak_symbol_block id) Ptrofs.zero)
 (f:=Internal fd) (vargs:=vargs) (vres:=v).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact Symbol]|apply deref_loc_reference;reflexivity].
 - exact Args.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_elements_taptweak_short_tag (Copy:memcpy_model) bytes e le m br bc bs bt:
 e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->
 e!__res__1=Some (br,Tstruct _sha256_context noattr) ->
 e!_ctx=Some (bc,Tstruct _sha256_context noattr) ->e!_taptweakTag=Some (bs,Tstruct _sha256_midstate noattr) ->
 le!_tagName__3=Some (Vptr bt Ptrofs.zero) ->le!_tagLen=Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
 NoDup [br;bc;bs] ->bt<>br ->bt<>bc ->bt<>bs ->(length bytes<56)%nat ->
 elements_taptweak_sha_startup m ->uint8_array_at m bt 0 bytes ->
 Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
 Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m taptweak_tag_stmt E0 le mf Out_normal /\
 uint32_array_at mf bs 0 (short_tag_regs bytes) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\
 elements_taptweak_sha_startup mf /\uint8_array_at mf bt 0 bytes.
Proof.
 intros InitGlobal AbsGlobal FinGlobal Result Context State TagName TagLen Sep TR TC TS Short Startup Bytes FR FC FS.
 pose proof (Nat2Z.is_nonneg (length bytes)) as Nonnegative.
 pose proof (proj1 (Nat2Z.inj_lt (length bytes) 56) Short) as Length.
 change (Z.of_nat (length bytes)<56) in Length.
 destruct (exec_elements_taptweak_sha_init_copy __res__1 _ctx _taptweakTag e le m br bc bs
 InitGlobal Result Context State Sep FR FC FS) as
 (m1 & Init & Pointer1 & Counter1 & Overflow1 & IV1 & FR1 & FC1 & FS1 & Frame1 & Read1).
 assert (Startup1:elements_taptweak_sha_startup m1).
 { destruct (elements_taptweak_sha_startup_separate m br 88 Startup ltac:(lia) FR) as [RD _].
 destruct (elements_taptweak_sha_startup_separate m bc 88 Startup ltac:(lia) FC) as [CD _].
 destruct (elements_taptweak_sha_startup_separate m bs 32 Startup ltac:(lia) FS) as [SD _].
 eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact Read1|exact Frame1|intros;repeat split;congruence]. }
 assert (TagBytes:forall i,(i<length bytes)%nat ->
 Mem.load Mint8unsigned m1 bt (Ptrofs.unsigned Ptrofs.zero+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))).
 { intros i Index;pose proof (Bytes i _ (nth_error_nth' bytes Int.zero Index)) as Load.
 change (Mem.load Mint8unsigned m1 bt (0+Z.of_nat i)=Some (Vint (nth i bytes Int.zero))).
 rewrite (proj1 Frame1) by (first [eapply load_valid;exact Load|intros;repeat split;assumption]);exact Load. }
 destruct (eval_elements_taptweak_sha_absorb_short_counter Copy [] bytes 0 m1 bc bt Ptrofs.zero
 (Vptr bs Ptrofs.zero) ltac:(cbn;lia) ltac:(lia) ltac:(lia) eq_refl ltac:(congruence) Startup1 FC1
 ltac:(change (0+Z.of_nat (length bytes)<=18446744073709551615);lia)
 Pointer1 Counter1 Overflow1 ltac:(intros i Impossible;inversion Impossible) TagBytes) as
 (m2 & Absorb & Pointer2 & Counter2 & Overflow2 & Buffer2 & FC2 & Frame2 & Read2 & SHA2).
 assert (FS2:Mem.range_perm m2 bs 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FS1|exact Frame2|intros;distinct Sep]. }
 assert (FR2:Mem.range_perm m2 br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FR1|exact Frame2|intros;distinct Sep]. }
 assert (VS:Mem.valid_block m1 bs) by (eapply Mem.perm_valid_block;apply (FS1 0);clear;lia).
 assert (IV2:uint32_array_at m2 bs 0 sha256_iv_words).
 { intros i x Nth;rewrite (proj1 Frame2 Mint32 bs (0+4*Z.of_nat i) VS);[apply IV1;exact Nth|intros;distinct Sep]. }
 destruct (eval_elements_taptweak_sha_finalize_short Copy bytes sha256_iv_words (Z.of_nat (length bytes)) m2 bc bs
 Short eq_refl Nonnegative ltac:(lia) ltac:(apply Z.mod_small;lia) ltac:(distinct Sep)
 SHA2 FC2 FS2 Pointer2 IV2 Counter2 Overflow2 Buffer2) as
 (mf & Finalize & Output & PointerF & CounterF & OverflowF & FCF & FSF & FrameF & ReadF & SHAF).
 replace (Z.of_nat (length bytes)+64-Z.of_nat (length bytes)) with 64 in CounterF by lia.
 assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FR2|exact FrameF|intros;split;distinct Sep]. }
 assert (Frame:lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf).
 { eapply lframe_trans;[exact Frame1|];eapply lframe_trans;
 [eapply lframe_implies;[exact Frame2|intros b pos [NR [NC NS]] Valid;exact NC]|
 eapply lframe_implies;[exact FrameF|intros b pos [NR [NC NS]] Valid;split;assumption]]. }
 exists mf;split.
 - unfold taptweak_tag_stmt;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1);[exact Init|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2).
   + unfold taptweak_tag_absorb;eapply exec_elements_taptweak_sha_call with
     (vargs:=[Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero;Vlong (Int64.repr (Z.of_nat (length bytes)))]) (v:=Vint Int.one).
     * left;reflexivity.
     * exact AbsGlobal.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact TagName|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact TagLen|reflexivity|constructor].
     * exact Absorb.
   + unfold taptweak_tag_finalize;eapply exec_elements_taptweak_sha_call with (vargs:=[Vptr bc Ptrofs.zero]) (v:=Vint Int.one).
     * right;left;reflexivity.
     * exact FinGlobal.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|constructor].
     * exact Finalize.
 - split;[exact Output|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
   split;[exact FRF|];split;[exact FCF|];split;[exact FSF|];split;[exact Frame|];split.
   + eapply preserved_trans;[exact Read1|eapply preserved_trans;[exact Read2|exact ReadF]].
   + split;[exact SHAF|].
     intros i x Nth;pose proof (Bytes i x Nth) as Load.
     rewrite (proj1 Frame) by (first [eapply load_valid;exact Load|intros;repeat split;assumption]);exact Load.
Qed.

Require Import Simplicity.Digest C.jet_elements_taptweak_tag.
Theorem exec_elements_taptweak_tag (Copy:memcpy_model) e le m br bc bs bt:
 e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->
 e!__res__1=Some (br,Tstruct _sha256_context noattr) ->
 e!_ctx=Some (bc,Tstruct _sha256_context noattr) ->e!_taptweakTag=Some (bs,Tstruct _sha256_midstate noattr) ->
 le!_tagName__3=Some (Vptr bt Ptrofs.zero) ->le!_tagLen=Some (Vlong (Int64.repr 17)) ->
 NoDup [br;bc;bs] ->bt<>br ->bt<>bc ->bt<>bs ->
 elements_taptweak_sha_startup m ->uint8_array_at m bt 0 elements_taptweak_tag_bytes ->
 Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
 Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m taptweak_tag_stmt E0 le mf Out_normal /\
 uint32_array_at mf bs 0 (Digest.hash256_reg elements_taptweak_tag_digest) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\
 elements_taptweak_sha_startup mf /\uint8_array_at mf bt 0 elements_taptweak_tag_bytes.
Proof.
 intros IG AG FG Result Context State Name Len Sep TR TC TS Startup Bytes FR FC FS.
 destruct (exec_elements_taptweak_short_tag Copy elements_taptweak_tag_bytes e le m br bc bs bt
 IG AG FG Result Context State Name ltac:(rewrite elements_taptweak_tag_length;exact Len)
 Sep TR TC TS ltac:(rewrite elements_taptweak_tag_length;lia) Startup Bytes FR FC FS)
 as (mf & Run & Output & Rest).
 exists mf;split;[exact Run|].
 rewrite elements_taptweak_tag_regs in Output;split;[exact Output|exact Rest].
Qed.
