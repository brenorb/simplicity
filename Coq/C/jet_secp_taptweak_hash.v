(** Canonical TapTweak message hash and the original hash/finalize/digest calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.SHA256.
Require Import C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_mem C.jet_uint32_array_init
 C.jet_buffer_input C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_sha_finalize_exec C.jet_sha_be32_write
 C.jet_secp_taptweak_tag C.jet_secp_sha_hash32 C.jet_secp_sha_append32 C.jet_memcpy_model
 C.jet_secp_sha_finalize_short C.jet_secp_sha_owned C.jet_secp_sha_startup
 C.jet_secp_schnorr_challenge_hash C.jet_bitcoin_build_tapleaf_spec
 C.jet_secp_curve_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_pad_word:Ty.tySem (Word 9):=@fromZ (WordToZ 9) (2^511+1024).
Definition taptweak_hash_word (pk h:Ty.tySem (Word 8)):=
 @Simplicity.SHA256.hashBlock Alg.CoreFunSem
 (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (taptweak_iv_word,(pk,h)),taptweak_pad_word).
Lemma taptweak_pad_bytes:map word8_array_value (vector_values (Word 3) 6 taptweak_pad_word)=sha_pad (Int64.repr 128).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_hash_bytes_word w:secp_hash_bytes (state_regs w)=schnorr_word_bytes w.
Proof. rewrite secp_hash_bytes_value,be_bytes_state_regs;reflexivity. Qed.
Lemma taptweak_hash_registers pk h:
 state_regs (taptweak_hash_word pk h)=
 SHA256.hash_block (SHA256.hash_block (state_regs taptweak_iv_word)
 (be_words (schnorr_word_bytes pk++schnorr_word_bytes h))) (be_words (sha_pad (Int64.repr 128))).
Proof.
 unfold taptweak_hash_word;rewrite hashBlock_regs,taptweak_pad_bytes,schnorr_hash_pair_registers;reflexivity.
Qed.
Local Opaque secp_ge.
Local Ltac distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem eval_taptweak_message_hash (Copy:memcpy_model) (pk h:Ty.tySem (Word 8)) m bc bs bt bb:
 NoDup [bc;bs;bt;bb] ->secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 Mem.range_perm m bt 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 uint32_array_at m bt 0 (state_regs h) ->Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->
 uint32_array_at m bs 0 (state_regs taptweak_iv_word) ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 96)) ->Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i (schnorr_word_bytes pk) Int.zero))) ->
 exists m1 m2 mf,
 Clight2.eval_funcall secp_ge m (Internal f_sha256_hash) [Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m1 Vundef /\
 Clight2.eval_funcall secp_ge m1 (Internal f_sha256_finalize) [Vptr bc Ptrofs.zero] E0 m2 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m2 (Internal f_sha256_fromMidstate) [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
 uint8_array_at mf bb 0 (schnorr_word_bytes (taptweak_hash_word pk h)) /\
 uint32_array_at mf bs 0 (state_regs (taptweak_hash_word pk h)) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 192)) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 Mem.range_perm mf bt 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 uint32_array_at mf bt 0 (state_regs h) /\
 lframe (fun b _=>b<>bc /\b<>bs /\b<>bb) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Sep Startup FC FS FT FB HashInput Pointer State Counter Overflow Buffer.
 assert (HashSep:NoDup [bc;bs;bt]) by
 (clear -Sep;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;repeat constructor;cbn [In];intuition congruence).
 destruct (eval_secp_sha_hash32 Copy (schnorr_word_bytes pk) (state_regs taptweak_iv_word) (state_regs h) 96 m bc bs bt
 ltac:(right;apply schnorr_word_bytes_length) (schnorr_state_regs_length _) (schnorr_state_regs_length _)
 ltac:(lia) ltac:(lia) ltac:(rewrite schnorr_word_bytes_length;reflexivity) HashSep Startup FC FS FT HashInput
 Pointer State Counter Overflow ltac:(rewrite schnorr_word_bytes_length;exact Buffer)) as
 (m1 & Hash & State1 & Pointer1 & Counter1 & Overflow1 & Buffer1 & FC1 & FS1 & FT1 & HashInput1 & Frame1 & Read1 & SHA1).
 unfold sha_append32_regs in State1;rewrite schnorr_word_bytes_length in State1;cbn [Nat.eqb] in State1.
 rewrite secp_hash_bytes_word in State1.
 assert (LFirst:length (SHA256.hash_block (state_regs taptweak_iv_word)
 (be_words (schnorr_word_bytes pk++schnorr_word_bytes h)))=8%nat).
 { rewrite <-schnorr_hash_pair_registers;apply schnorr_state_regs_length. }
 destruct (eval_secp_sha_finalize_short Copy []
 (SHA256.hash_block (state_regs taptweak_iv_word) (be_words (schnorr_word_bytes pk++schnorr_word_bytes h)))
 128 m1 bc bs ltac:(cbn;lia) LFirst ltac:(lia) ltac:(cbn;lia) eq_refl ltac:(distinct Sep)
 SHA1 FC1 FS1 Pointer1 State1 Counter1 Overflow1 ltac:(intros i Impossible;inversion Impossible)) as
 (m2 & Finalize & State2 & Pointer2 & Counter2 & Overflow2 & FC2 & FS2 & Frame2 & Read2 & SHA2).
 change (uint32_array_at m2 bs 0 (SHA256.hash_block (SHA256.hash_block (state_regs taptweak_iv_word)
 (be_words (schnorr_word_bytes pk++schnorr_word_bytes h))) (be_words (sha_pad (Int64.repr 128))))) in State2.
 rewrite <-taptweak_hash_registers in State2.
 assert (FB1:Mem.range_perm m1 bb 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FB|exact Frame1|intros;split;distinct Sep]. }
 assert (FB2:Mem.range_perm m2 bb 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FB1|exact Frame2|intros;split;distinct Sep]. }
 assert (FT2:Mem.range_perm m2 bt 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FT1|exact Frame2|intros;split;distinct Sep]. }
 assert (VT1:Mem.valid_block m1 bt) by (eapply Mem.perm_valid_block;apply (FT1 0);clear;lia).
 assert (HashInput2:uint32_array_at m2 bt 0 (state_regs h)).
 { intros i x Nth;rewrite (proj1 Frame2 Mint32 bt (0+4*Z.of_nat i) VT1);
 [apply HashInput1;exact Nth|intros;split;distinct Sep]. }
 destruct (eval_secp_sha_digest_owned (state_regs (taptweak_hash_word pk h)) m2 bb bs
 (schnorr_state_regs_length _) ltac:(distinct Sep) State2 FB2 FS2) as
 (mf & Digest & Bytes & StateF & FBF & FSF & FrameF & ReadF).
 assert (VC2:Mem.valid_block m2 bc) by (eapply Mem.perm_valid_block;apply (FC2 0);clear;lia).
 assert (VT2:Mem.valid_block m2 bt) by (eapply Mem.perm_valid_block;apply (FT2 0);clear;lia).
 assert (SHAF:secp_sha_startup mf).
 { eapply secp_sha_startup_preserved;[exact SHA2|exact ReadF|exact FrameF|].
 intros pos;pose proof (proj1 (secp_sha_startup_separate m2 bb 32 SHA2 ltac:(lia) FB2));congruence. }
 exists m1,m2,mf;split;[exact Hash|];split;[exact Finalize|];split;[exact Digest|];split.
 - intros i x Nth.
   assert (Index:(i<32)%nat) by (rewrite <-(schnorr_word_bytes_length (taptweak_hash_word pk h));apply nth_error_Some;rewrite Nth;discriminate).
   pose proof (Bytes i Index) as Byte.
   unfold secp_sha_digest_bytes in Byte.
   change (Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint
    (Int.repr (nth i (map Int.unsigned (C.jet_sha_be32_write.be_bytes (state_regs (taptweak_hash_word pk h)))) (Int.unsigned Int.zero))))) in Byte.
   rewrite map_nth,Int.repr_unsigned,be_bytes_state_regs in Byte.
   change (Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (nth i (schnorr_word_bytes (taptweak_hash_word pk h)) Int.zero))) in Byte.
   pose proof (nth_error_nth _ _ Int.zero Nth) as Value.
   rewrite Value in Byte;exact Byte.

 - split;[exact StateF|];split.
   + rewrite (proj1 FrameF Mptr bc 0 VC2);[exact Pointer2|intros;distinct Sep].
   + split.
     * rewrite (proj1 FrameF Mint64 bc 8 VC2);[exact Counter2|intros;distinct Sep].
     * split.
       -- rewrite (proj1 FrameF Mint8unsigned bc 80 VC2);[exact Overflow2|intros;distinct Sep].
       -- split.
          ++ eapply curve_keep_free;[clear;lia|exact FC2|exact FrameF|intros;distinct Sep].
          ++ split;[exact FSF|];split.
             ** eapply curve_keep_free;[clear;lia|exact FT2|exact FrameF|intros;distinct Sep].
             ** split;[exact FBF|];split.
                --- intros i x Nth;rewrite (proj1 FrameF Mint32 bt (0+4*Z.of_nat i) VT2);[apply HashInput2;exact Nth|intros;distinct Sep].
                --- split.
                    +++ eapply lframe_trans.
                        { eapply lframe_implies;[exact Frame1|intros b pos [NC [NS NB]] Valid;split;assumption]. }
                        eapply lframe_trans; eapply lframe_implies;
                        [exact Frame2|intros b pos [NC [NS NB]] Valid;split;assumption|
                        exact FrameF|intros b pos [NC [NS NB]] Valid;exact NB].
                    +++ split.
                        { eapply preserved_trans;[exact Read1|].
                          eapply preserved_trans;[exact Read2|exact ReadF]. }
                        exact SHAF.
Qed.

Require Import C.jet_secp_curve_statements C.jet_secp_sha_init_copy C.jet_secp_generator_sha_start
 C.jet_secp_taptweak_prefix C.jet_secp_schnorr_challenge_body C.jet_secp_root_chain_owned.
Definition taptweak_message_absorb:=curve_call _sha256_hash f_sha256_hash None
 [Eaddrof (Evar _ctx__1 generator_sha_ctx_type) (tptr generator_sha_ctx_type);
  Eaddrof (Evar _input_hash generator_sha_state_type) (tptr generator_sha_state_type)].
Definition taptweak_message_finalize:=curve_call _sha256_finalize f_sha256_finalize None
 [Eaddrof (Evar _ctx__1 generator_sha_ctx_type) (tptr generator_sha_ctx_type)].
Definition taptweak_message_digest:=curve_call _sha256_fromMidstate f_sha256_fromMidstate None
 [Evar _buf (tarray tuchar 32);Efield (Evar _output_hash generator_sha_state_type) _s (tarray tuint 8)].
Definition taptweak_message_hash_stmt:=Ssequence taptweak_message_absorb
 (Ssequence taptweak_message_finalize taptweak_message_digest).
Lemma taptweak_message_hash_source:
 root_drop_statements 8 (fn_body f_simplicity_generic_taptweak)=
 Ssequence taptweak_message_absorb (Ssequence taptweak_message_finalize
 (Ssequence taptweak_message_digest (root_drop_statements 11 (fn_body f_simplicity_generic_taptweak)))).
Proof. reflexivity. Qed.
Lemma exec_taptweak_hash_calls e le m m1 m2 mf bc bs bt bb:
 e!_sha256_hash=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
 e!_ctx__1=Some (bc,generator_sha_ctx_type) ->e!_output_hash=Some (bs,generator_sha_state_type) ->
 e!_input_hash=Some (bt,generator_sha_state_type) ->e!_buf=Some (bb,tarray tuchar 32) ->
 Clight2.eval_funcall secp_ge m (Internal f_sha256_hash) [Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m1 Vundef ->
 Clight2.eval_funcall secp_ge m1 (Internal f_sha256_finalize) [Vptr bc Ptrofs.zero] E0 m2 (Vint Int.one) ->
 Clight2.eval_funcall secp_ge m2 (Internal f_sha256_fromMidstate) [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m taptweak_message_hash_stmt E0 le mf Out_normal.
Proof.
 intros HG FG DG Context State Input Buf Hash Finalize Digest.
 unfold taptweak_message_hash_stmt;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1).
 - unfold taptweak_message_absorb,curve_call.
   eapply exec_Scall with (vf:=Vptr (secp_symbol_block _sha256_hash) Ptrofs.zero) (f:=Internal f_sha256_hash)
   (vargs:=[Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero]) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue.
     { eapply eval_Evar_global;[exact HG|exact taptweak_hash_symbol]. }
     apply deref_loc_reference;reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Input|reflexivity|constructor].
   + exact taptweak_hash_function.
   + reflexivity.
   + exact Hash.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2).
   + unfold taptweak_message_finalize;eapply exec_schnorr_challenge_call with
     (vargs:=[Vptr bc Ptrofs.zero]) (v:=Vint Int.one).
     * right;right;left;reflexivity.
     * exact FG.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|constructor].
     * exact Finalize.
   + unfold taptweak_message_digest;eapply exec_schnorr_challenge_call with
     (vargs:=[Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
     * right;right;right;left;reflexivity.
     * exact DG.
     * eapply eval_Econs.
       { eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]. }
       { reflexivity. }
       eapply eval_Econs;[apply eval_sha_local_state;exact State|reflexivity|constructor].
     * exact Digest.
Qed.
