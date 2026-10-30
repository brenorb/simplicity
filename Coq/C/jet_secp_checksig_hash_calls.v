(** Actual CheckSig absorption/finalization/serialization statement suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word
 C.jets_secp C.jet_secp_linkage C.jet_secp_curve_statements C.jet_secp_root_chain_owned
 C.jet_secp_checksig_hash C.jet_secp_checksig_context C.jet_secp_schnorr_challenge_hash
 C.jet_secp_schnorr_challenge_absorb C.jet_secp_schnorr_challenge_body
 C.jet_secp_sha_startup C.jet_secp_sha_owned C.jet_sha_ctx8_model C.jet_sha_word_bytes
 C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init C.jet_clight_internal_preserve
 C.jet_secp_schnorr_challenge_owned C.jet_secp_schnorr_challenge_entry.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition checksig_absorb_call:=curve_call _sha256_uchars f_sha256_uchars None
 [Eaddrof (Evar _ctx (Tstruct _sha256_context noattr)) (tptr (Tstruct _sha256_context noattr));
  Evar _msg (tarray tuchar 64);Econst_int (Int.repr 64) tint].
Definition checksig_finalize_call:=curve_call _sha256_finalize f_sha256_finalize None
 [Eaddrof (Evar _ctx (Tstruct _sha256_context noattr)) (tptr (Tstruct _sha256_context noattr))].
Definition checksig_digest_call:=curve_call _sha256_fromMidstate f_sha256_fromMidstate None
 [Evar _buf (tarray tuchar 32);checksig_output_expr].
Definition checksig_hash_calls:=Ssequence checksig_absorb_call (Ssequence checksig_finalize_call checksig_digest_call).
Lemma checksig_hash_calls_source:
 match root_drop_statements 3 (fn_body f_simplicity_check_sig_verify) with
 | Ssequence (Ssequence _ (Ssequence _ calls)) _=>calls|_=>Sskip end=checksig_hash_calls.
Proof. reflexivity. Qed.
Lemma checksig_digest_word_bytes h:
 map Int.repr (secp_sha_digest_bytes (state_regs h))=schnorr_word_bytes h.
Proof.
 unfold secp_sha_digest_bytes;rewrite sha_state_be_bytes,map_map.
 transitivity (map (fun x:int=>x) (schnorr_word_bytes h)).
 - apply map_ext;intro x;apply Int.repr_unsigned.
 - apply map_id.
Qed.
Local Opaque secp_ge.
Theorem exec_checksig_hash_calls (Model:memcpy_model) (ir h:Ty.tySem (Word 8)) e le m bc bs bm bb:
 e!_ctx=Some (bc,Tstruct _sha256_context noattr) ->e!_output=Some (bs,Tstruct _sha256_midstate noattr) ->
 e!_msg=Some (bm,tarray tuchar 64) ->e!_buf=Some (bb,tarray tuchar 32) ->
 e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
 bc<>bs ->bc<>bm ->bb<>bc ->bb<>bs ->secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->
 uint32_array_at m bs 0 (state_regs C.jet_secp_checksig_tag.checksig_iv_word) ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 64)) ->Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 schnorr_bytes_at m bm Ptrofs.zero (schnorr_word_bytes ir++schnorr_word_bytes h) ->exists mf,
 Clight2.exec_stmt secp_ge e le m checksig_hash_calls E0 le mf Out_normal /\
 schnorr_bytes_at mf bb Ptrofs.zero (schnorr_word_bytes (checksig_hash_word ir h)) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs /\b<>bb) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Context Output Msg Buf US FS DS CS CM BC BS Ready FC FO FB Pointer State Counter Overflow Bytes.
 destruct (eval_checksig_sha_calls Model ir h m bc bs bm Ptrofs.zero CS CM Ready FC FO
  ltac:(clear;change (64<=18446744073709551615);lia) Pointer State Counter Overflow Bytes)
 as (m1 & mh & Absorb & Final & StateH & PointerH & CounterH & OverflowH & FCH & FOH & FrameH & ReadH & ReadyH).
 assert (FBH:Mem.range_perm mh bb 0 32 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameH|intros;split;assumption|exact FB]. }
 destruct (eval_secp_sha_digest_owned (state_regs (checksig_hash_word ir h)) mh bb bs
  (schnorr_state_regs_length _) BS StateH FBH FOH)
 as (mf & Digest & DigestBytes & StateF & FBF & FOF & FrameF & ReadF).
 assert (FCF:Mem.range_perm mf bc 0 88 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameF|intros;congruence|exact FCH]. }
 exists mf;split.
 - unfold checksig_hash_calls;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1).
   + unfold checksig_absorb_call;eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
     [right;left;reflexivity|exact US| |exact Absorb].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
     eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Msg|apply deref_loc_reference;reflexivity]|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|constructor].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mh).
     * unfold checksig_finalize_call;eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
       [right;right;left;reflexivity|exact FS| |exact Final].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|constructor].
     * unfold checksig_digest_call;eapply exec_schnorr_challenge_call with (v:=Vundef);
       [right;right;right;left;reflexivity|exact DS| |exact Digest].
       eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;exact Buf|apply deref_loc_reference;reflexivity]|reflexivity|].
       eapply eval_Econs;[apply eval_checksig_output;exact Output|reflexivity|constructor].
 - split.
   + intros i Index;rewrite Ptrofs.unsigned_zero,Z.add_0_l.
     rewrite <-checksig_digest_word_bytes.
     change (Mem.load Mint8unsigned mf bb (Z.of_nat i)=
       Some (Vint (nth i (map Int.repr (secp_sha_digest_bytes (state_regs (checksig_hash_word ir h)))) (Int.repr 0)))).
     rewrite map_nth;apply DigestBytes;rewrite schnorr_word_bytes_length in Index;exact Index.
   + split;[exact FCF|];split;[exact FOF|];split;[exact FBF|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameH|intros b pos [C [S B]] Old;split;assumption].
       -- eapply lframe_implies;[exact FrameF|intros b pos [C [S B]] Old;exact B].
     * split;[eapply preserved_trans;[exact ReadH|exact ReadF]|].
       eapply secp_sha_startup_preserved;[exact ReadyH|exact ReadF|exact FrameF|].
       pose proof (proj1 (secp_sha_startup_separate mh bb 32 ReadyH ltac:(lia) FBH)) as Apart.
       intros;congruence.
Qed.
