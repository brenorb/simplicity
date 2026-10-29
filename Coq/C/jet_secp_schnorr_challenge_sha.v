(** The four original hashing calls after the challenge context is initialized.
    The real caller uses a separate constructor return slot and struct copy;
    these, fromMidstate/scalar conversion and cleanup remain caller obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init C.jet_sha_ctx8_model
 C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_secp_sha_startup
 C.jet_secp_sha_finalize_short C.jet_secp_schnorr_tagged_spec
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_schnorr_challenge_sha_calls (Hmodel:memcpy_model)
 (r pk msg:Ty.tySem (Word 8)) m bc bs br bp bm or op om :
 bc<>bs -> bc<>br -> bc<>bp -> bc<>bm -> bs<>bm ->
 secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 Ptrofs.unsigned or+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned op+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned om+32<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->
 uint32_array_at m bs 0 (state_regs schnorr_challenge_iv_word) ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 64)) ->
 Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 schnorr_bytes_at m br or (schnorr_word_bytes r) ->
 schnorr_bytes_at m bp op (schnorr_word_bytes pk) ->
 schnorr_bytes_at m bm om (schnorr_word_bytes msg) ->exists m1 m2 m3 mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr br or;Vlong (Int64.repr 32)] E0 m1 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m1 (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bp op;Vlong (Int64.repr 32)] E0 m2 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m2 (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bm om;Vlong (Int64.repr 32)] E0 m3 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m3 (Internal jets_secp.f_sha256_finalize)
  [Vptr bc Ptrofs.zero] E0 mf (Vint Int.one) /\
 uint32_array_at mf bs 0 (state_regs (schnorr_challenge_hash_word r pk msg)) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 192)) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros CS CR CP CM SM Startup FC FS RHi PHi MHi Pointer0 State0 Counter0 Overflow0 RB0 PB0 MB0.
 destruct (eval_schnorr_challenge_absorb Hmodel (schnorr_word_bytes r) (schnorr_word_bytes pk)
  (schnorr_word_bytes msg) (state_regs schnorr_challenge_iv_word) m bc bs br bp bm or op om
  (schnorr_word_bytes_length r) (schnorr_word_bytes_length pk) (schnorr_word_bytes_length msg)
  (schnorr_state_regs_length schnorr_challenge_iv_word) CS CR CP CM SM Startup FC FS
  RHi PHi MHi Pointer0 State0 Counter0 Overflow0 RB0 PB0 MB0) as
  (m1 & m2 & m3 & Call1 & Call2 & Call3 & State3 & Pointer3 & Counter3 & Overflow3 & Buffer3 & FC3 & FS3 & Frame3 & Readonly3 & Startup3).
 assert (LFirst:length (SHA256.hash_block (state_regs schnorr_challenge_iv_word)
  (be_words (schnorr_word_bytes r++schnorr_word_bytes pk)))=8%nat).
 { rewrite <-schnorr_hash_pair_registers;apply schnorr_state_regs_length. }
 destruct (eval_secp_sha_finalize_short Hmodel (schnorr_word_bytes msg)
  (SHA256.hash_block (state_regs schnorr_challenge_iv_word) (be_words (schnorr_word_bytes r++schnorr_word_bytes pk)))
  160 m3 bc bs ltac:(rewrite schnorr_word_bytes_length;lia) LFirst ltac:(lia)
  ltac:(rewrite schnorr_word_bytes_length;lia) ltac:(rewrite schnorr_word_bytes_length;reflexivity)
  CS Startup3 FC3 FS3 Pointer3 State3 Counter3 Overflow3
  ltac:(rewrite schnorr_word_bytes_length;exact Buffer3)) as
  (mf & Finalize & Output & PointerF & CounterF & OverflowF & FCF & FSF & FrameF & ReadonlyF & StartupF).
 rewrite schnorr_word_bytes_length in CounterF.
 exists m1,m2,m3,mf;split;[exact Call1|];split;[exact Call2|];
 split;[exact Call3|];split;[exact Finalize|];split.
 - rewrite schnorr_challenge_hash_registers;exact Output.
 - split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];split;[exact FCF|];split;[exact FSF|];split.
   + eapply lframe_trans;[exact Frame3|exact FrameF].
   + split;[eapply preserved_trans;[exact Readonly3|exact ReadonlyF]|exact StartupF].
Qed.
