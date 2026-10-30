(** The original runtime TapTweak tag-hashing block, including the real struct copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Digest.
Require Import C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_mem C.jet_read8s_layout
 C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha_ctx8_model C.jet_memcpy_model
 C.jet_secp_generator_sha_start C.jet_secp_taptweak_tag C.jet_secp_sha_init_copy C.jet_secp_sha_absorb_short
 C.jet_secp_sha_finalize_short C.jet_secp_schnorr_challenge_body C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_schnorr_startup C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_tag_absorb:=curve_call _sha256_uchars f_sha256_uchars None
 [Eaddrof (Evar _ctx generator_sha_ctx_type) (tptr generator_sha_ctx_type);
  Etempvar _tagName__3 (tptr tuchar);Etempvar _tagLen tulong].
Definition taptweak_tag_finalize:=curve_call _sha256_finalize f_sha256_finalize None
 [Eaddrof (Evar _ctx generator_sha_ctx_type) (tptr generator_sha_ctx_type)].
Definition taptweak_tag_stmt:=Ssequence (sha_init_copy_stmt __res__1 _ctx _taptweakTag)
 (Ssequence taptweak_tag_absorb taptweak_tag_finalize).
Lemma taptweak_tag_stmt_source:
 match fn_body f_simplicity_generic_taptweak with Ssequence first _=>first|_=>Sskip end=taptweak_tag_stmt.
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_taptweak_tag (Copy:memcpy_model) e le m br bc bs:
 e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->
 e!__res__1=Some (br,generator_sha_ctx_type) ->e!_ctx=Some (bc,generator_sha_ctx_type) ->
 e!_taptweakTag=Some (bs,generator_sha_state_type) ->
 le!_tagName__3=Some (Vptr taptweak_tag_block Ptrofs.zero) ->le!_tagLen=Some (Vlong (Int64.repr 8)) ->
 NoDup [br;bc;bs] ->taptweak_startup m ->
 Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
 Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.exec_stmt secp_ge e le m taptweak_tag_stmt E0 le mf Out_normal /\
 uint32_array_at mf bs 0 (Digest.hash256_reg taptweak_tag_digest) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\taptweak_startup mf.
Proof.
 intros InitGlobal AbsGlobal FinGlobal Result Context State TagName TagLen Sep Startup FR FC FS.
 destruct (exec_sha_init_copy __res__1 _ctx _taptweakTag e le m br bc bs
 InitGlobal Result Context State Sep FR FC FS) as
 (m1 & Init & Pointer1 & Counter1 & Overflow1 & IV1 & FR1 & FC1 & FS1 & Frame1 & Read1).
 assert (Forward1:mem_forward m m1) by (eapply (proj1 (clight_exec_forward secp_ge));exact Init).
 assert (Startup1:taptweak_startup m1).
 { eapply taptweak_startup_owned_forward with (slots:=[(br,88);(bc,88);(bs,32)]);
 [exact Startup|exact Forward1| |].
 - intros b hi [Pair|[Pair|[Pair|[]]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact Frame1|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 assert (TagSep:bc<>taptweak_tag_block) by
 (eapply taptweak_tag_owned_separate with (m:=m1) (size:=88);[exact (proj2 Startup1)|clear;lia|exact FC1]).
 assert (TagBytes:forall i,(i<length taptweak_tag_bytes)%nat ->
 Mem.load Mint8unsigned m1 taptweak_tag_block (Ptrofs.unsigned Ptrofs.zero+Z.of_nat i)=Some (Vint (nth i taptweak_tag_bytes Int.zero))).
 { intros i Index;apply (proj1 (proj2 Startup1));apply nth_error_nth';exact Index. }
 destruct (eval_secp_sha_absorb_short_counter Copy [] taptweak_tag_bytes 0 m1 bc taptweak_tag_block Ptrofs.zero
 (Vptr bs Ptrofs.zero) ltac:(rewrite taptweak_tag_length;cbn;lia) ltac:(lia)
 ltac:(rewrite taptweak_tag_length;cbn;lia) eq_refl TagSep (proj2 (proj2 (proj1 Startup1))) FC1
 ltac:(rewrite taptweak_tag_length;change (8<=18446744073709551615);lia)
 Pointer1 Counter1 Overflow1 ltac:(intros i Impossible;inversion Impossible) TagBytes) as
 (m2 & Absorb & Pointer2 & Counter2 & Overflow2 & Buffer2 & FC2 & Frame2 & Read2 & SHA2).
 rewrite taptweak_tag_length in Counter2.
 assert (FS2:Mem.range_perm m2 bs 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FS1|exact Frame2|intros;distinct Sep]. }
 assert (FR2:Mem.range_perm m2 br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FR1|exact Frame2|intros;distinct Sep]. }
 assert (VS:Mem.valid_block m1 bs) by (eapply Mem.perm_valid_block;apply (FS1 0);clear;lia).
 assert (IV2:uint32_array_at m2 bs 0 sha256_iv_words).
 { intros i x Nth;rewrite (proj1 Frame2 Mint32 bs (0+4*Z.of_nat i) VS);
 [apply IV1;exact Nth|intros;distinct Sep]. }
 assert (Forward2:mem_forward m1 m2) by (eapply (proj2 (clight_exec_forward secp_ge));exact Absorb).
 assert (Startup2:taptweak_startup m2).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88)]);
 [exact Startup1|exact Forward2| |].
 - intros b hi [Pair|[]];inversion Pair;subst;split;[clear;lia|exact FC1].
 - eapply lframe_implies;[exact Frame2|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 destruct (eval_secp_sha_finalize_short Copy taptweak_tag_bytes sha256_iv_words 8 m2 bc bs
 ltac:(rewrite taptweak_tag_length;lia) eq_refl ltac:(lia)
 ltac:(rewrite taptweak_tag_length;cbn;lia) ltac:(rewrite taptweak_tag_length;reflexivity)
 ltac:(distinct Sep) SHA2 FC2 FS2 Pointer2 IV2 Counter2 Overflow2 Buffer2) as
 (mf & Finalize & Output & PointerF & CounterF & OverflowF & FCF & FSF & FrameF & ReadF & SHAF).
 rewrite taptweak_tag_length in CounterF;change (Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64))) in CounterF.
 rewrite taptweak_tag_regs in Output.
 assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FR2|exact FrameF|intros;split;distinct Sep]. }
 assert (ForwardF:mem_forward m2 mf) by (eapply (proj2 (clight_exec_forward secp_ge));exact Finalize).
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88);(bs,32)]);
 [exact Startup2|exact ForwardF| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact FrameF|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 exists mf;split.
 - unfold taptweak_tag_stmt;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1);[exact Init|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2).
   + unfold taptweak_tag_absorb;eapply exec_schnorr_challenge_call with
     (vargs:=[Vptr bc Ptrofs.zero;Vptr taptweak_tag_block Ptrofs.zero;Vlong (Int64.repr 8)]) (v:=Vint Int.one).
     * right;left;reflexivity.
     * exact AbsGlobal.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact TagName|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact TagLen|reflexivity|constructor].
     * exact Absorb.
   + unfold taptweak_tag_finalize;eapply exec_schnorr_challenge_call with
     (vargs:=[Vptr bc Ptrofs.zero]) (v:=Vint Int.one).
     * right;right;left;reflexivity.
     * exact FinGlobal.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|constructor].
     * exact Finalize.
 - split;[exact Output|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
   split;[exact FRF|];split;[exact FCF|];split;[exact FSF|];split.
   + eapply lframe_trans;[exact Frame1|];eapply lframe_trans;
     [eapply lframe_implies;[exact Frame2|intros b pos [NR [NC NS]] Valid;exact NC]|
      eapply lframe_implies;[exact FrameF|intros b pos [NR [NC NS]] Valid;split;assumption]].
   + split;[eapply preserved_trans;[exact Read1|eapply preserved_trans;[exact Read2|exact ReadF]]|exact StartupF].
Qed.
