(** Original output context construction and both TapTweak tag-hash calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Digest.
Require Import C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_mem C.jet_uint32_array_init
 C.jet_sha256_iv_init C.jet_sha_ctx8_model C.jet_memcpy_model C.jet_secp_sha_owned
 C.jet_secp_taptweak_tag C.jet_secp_taptweak_tag_exec C.jet_secp_sha_init_copy C.jet_secp_generator_sha_start
 C.jet_secp_sha_hash32 C.jet_secp_sha_append32 C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_schnorr_startup C.jet_secp_statement_prefix C.jet_secp_root_chain_owned C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_prefix_hash:=curve_call _sha256_hash f_sha256_hash None
 [Eaddrof (Evar _ctx__1 generator_sha_ctx_type) (tptr generator_sha_ctx_type);
  Eaddrof (Evar _taptweakTag generator_sha_state_type) (tptr generator_sha_state_type)].
Definition taptweak_output_prefix:=Ssequence (sha_init_copy_stmt __res _ctx__1 _output_hash)
 (Ssequence taptweak_prefix_hash taptweak_prefix_hash).
Lemma taptweak_prefix_source:
 fn_body f_simplicity_generic_taptweak=Ssequence taptweak_tag_stmt
 (Ssequence (sha_init_copy_stmt __res _ctx__1 _output_hash)
 (Ssequence taptweak_prefix_hash (Ssequence taptweak_prefix_hash
 (root_drop_statements 4 (fn_body f_simplicity_generic_taptweak))))).
Proof. reflexivity. Qed.
Lemma taptweak_hash_symbol:Genv.find_symbol secp_ge _sha256_hash=Some (secp_symbol_block _sha256_hash).
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_hash_function:Genv.find_funct secp_ge (Vptr (secp_symbol_block _sha256_hash) Ptrofs.zero)=Some (Internal f_sha256_hash).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Lemma exec_taptweak_prefix_hash e le m mf bc bt:
 e!_sha256_hash=None ->e!_ctx__1=Some (bc,generator_sha_ctx_type) ->e!_taptweakTag=Some (bt,generator_sha_state_type) ->
 Clight2.eval_funcall secp_ge m (Internal f_sha256_hash) [Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m taptweak_prefix_hash E0 le mf Out_normal.
Proof.
 intros Global Context Tag Call;unfold taptweak_prefix_hash,curve_call.
 eapply exec_Scall with (vf:=Vptr (secp_symbol_block _sha256_hash) Ptrofs.zero) (f:=Internal f_sha256_hash)
 (vargs:=[Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero]) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact taptweak_hash_symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Tag|reflexivity|constructor].
 - exact taptweak_hash_function.
 - reflexivity.
 - exact Call.
Qed.
Theorem exec_taptweak_output_prefix (Copy:memcpy_model) e le m br bc bs bt:
 e!_sha256_init=None ->e!_sha256_hash=None ->
 e!__res=Some (br,generator_sha_ctx_type) ->e!_ctx__1=Some (bc,generator_sha_ctx_type) ->
 e!_output_hash=Some (bs,generator_sha_state_type) ->e!_taptweakTag=Some (bt,generator_sha_state_type) ->
 NoDup [br;bc;bs;bt] ->taptweak_startup m ->
 Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
 Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bt 0 32 Cur Freeable ->
 uint32_array_at m bt 0 (Digest.hash256_reg taptweak_tag_digest) ->exists mf,
 Clight2.exec_stmt secp_ge e le m taptweak_output_prefix E0 le mf Out_normal /\
 uint32_array_at mf bs 0 (Digest.hash256_reg taptweak_tag_iv) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bt 0 32 Cur Freeable /\
 uint32_array_at mf bt 0 (Digest.hash256_reg taptweak_tag_digest) /\
 lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\taptweak_startup mf.
Proof.
 intros InitGlobal HashGlobal Result Context State Tag Sep Startup FR FC FS FT Tag0.
 assert (Sep3:NoDup [br;bc;bs]) by
 (clear -Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;repeat constructor;cbn [In];intuition congruence).
 destruct (exec_sha_init_copy __res _ctx__1 _output_hash e le m br bc bs InitGlobal Result Context State Sep3 FR FC FS)
 as (mi & Init & PointerI & CounterI & OverflowI & IV & FRI & FCI & FSI & FrameI & ReadI).
 assert (ForwardI:mem_forward m mi) by (eapply (proj1 (clight_exec_forward secp_ge));exact Init).
 assert (StartupI:taptweak_startup mi).
 { eapply taptweak_startup_owned_forward with (slots:=[(br,88);(bc,88);(bs,32)]);
 [exact Startup|exact ForwardI| |].
 - intros b hi [Pair|[Pair|[Pair|[]]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact FrameI|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 assert (FTI:Mem.range_perm mi bt 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FT|exact FrameI|intros;repeat split;distinct Sep]. }
 assert (VT:Mem.valid_block m bt) by (eapply Mem.perm_valid_block;apply (FT 0);clear;lia).
 assert (TagI:uint32_array_at mi bt 0 (Digest.hash256_reg taptweak_tag_digest)).
 { intros i x Nth;rewrite (proj1 FrameI Mint32 bt (0+4*Z.of_nat i) VT);
 [apply Tag0;exact Nth|intros;repeat split;distinct Sep]. }
 assert (HashSep:NoDup [bc;bs;bt]) by
 (clear -Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;repeat constructor;cbn [In];intuition congruence).
 destruct (eval_secp_sha_hash32 Copy [] sha256_iv_words (Digest.hash256_reg taptweak_tag_digest) 0 mi bc bs bt
 (or_introl eq_refl) eq_refl (Digest.hash256_len _) ltac:(lia) ltac:(lia) eq_refl HashSep
 (proj2 (proj2 (proj1 StartupI))) FCI FSI FTI TagI PointerI IV CounterI OverflowI ltac:(intros i Impossible;inversion Impossible)) as
 (m1 & Hash1 & State1 & Pointer1 & Counter1 & Overflow1 & Buffer1 & FC1 & FS1 & FT1 & Tag1 & Frame1 & Read1 & SHA1).
 change (uint32_array_at m1 bs 0 sha256_iv_words) in State1.
 change (Mem.load Mint64 m1 bc 8=Some (Vlong (Int64.repr 32))) in Counter1.
 change (forall i,(i<length (secp_hash_bytes (Digest.hash256_reg taptweak_tag_digest)))%nat ->
 Mem.load Mint8unsigned m1 bc (16+Z.of_nat i)=Some (Vint (nth i (secp_hash_bytes (Digest.hash256_reg taptweak_tag_digest)) Int.zero))) in Buffer1.
 destruct (eval_secp_sha_hash32 Copy (secp_hash_bytes (Digest.hash256_reg taptweak_tag_digest)) sha256_iv_words
 (Digest.hash256_reg taptweak_tag_digest) 32 m1 bc bs bt
 ltac:(right;apply secp_hash_bytes_length;apply Digest.hash256_len) eq_refl (Digest.hash256_len _)
 ltac:(lia) ltac:(lia) ltac:(rewrite secp_hash_bytes_length by apply Digest.hash256_len;reflexivity) HashSep SHA1
 FC1 FS1 FT1 Tag1 Pointer1 State1 Counter1 Overflow1 Buffer1) as
 (mf & Hash2 & StateF & PointerF & CounterF & OverflowF & BufferF & FCF & FSF & FTF & TagF & FrameF & ReadF & SHAF).
 unfold sha_append32_regs in StateF.
 rewrite secp_hash_bytes_length in StateF by apply Digest.hash256_len.
 cbn [Nat.eqb] in StateF.
 rewrite taptweak_iv_regs in StateF.
 assert (FR1:Mem.range_perm m1 br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FRI|exact Frame1|intros;split;distinct Sep]. }
 assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FR1|exact FrameF|intros;split;distinct Sep]. }
 assert (Forward1:mem_forward mi m1) by (eapply (proj2 (clight_exec_forward secp_ge));exact Hash1).
 assert (ForwardF:mem_forward m1 mf) by (eapply (proj2 (clight_exec_forward secp_ge));exact Hash2).
 assert (Startup1:taptweak_startup m1).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88);(bs,32)]);
 [exact StartupI|exact Forward1| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact Frame1|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 assert (StartupF:taptweak_startup mf).
 { eapply taptweak_startup_owned_forward with (slots:=[(bc,88);(bs,32)]);
 [exact Startup1|exact ForwardF| |].
 - intros b hi [Pair|[Pair|[]]];inversion Pair;subst;split;try (clear;lia);assumption.
 - eapply lframe_implies;[exact FrameF|intros b pos Outside Valid;cbn [map In fst] in Outside;cbn;intuition congruence]. }
 exists mf;split.
 - unfold taptweak_output_prefix;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi);[exact Init|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1);
   eapply exec_taptweak_prefix_hash;[exact HashGlobal|exact Context|exact Tag|exact Hash1|
   exact HashGlobal|exact Context|exact Tag|exact Hash2].
 - split;[exact StateF|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
   split;[exact FRF|];split;[exact FCF|];split;[exact FSF|];split;[exact FTF|];split;[exact TagF|];split.
   + eapply lframe_trans;[exact FrameI|];eapply lframe_trans;
     eapply lframe_implies;[exact Frame1|intros b pos [NR [NC NS]] Valid;split;assumption|
     exact FrameF|intros b pos [NR [NC NS]] Valid;split;assumption].
   + split;[eapply preserved_trans;[exact ReadI|eapply preserved_trans;[exact Read1|exact ReadF]]|exact StartupF].
Qed.
