(** The standard Signature message hash, using the original SHA calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg
 C.jet_secp_checksig_tag C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb
 C.jet_buffer_input C.jet_read8s_layout C.jet_sha_ctx8_model C.jet_sha_finalize_exec C.jet_memcpy_model C.jet_sx_mem
 C.jet_uint32_array_init C.jet_secp_linkage C.jet_secp_sha_startup
 C.jet_clight_internal_preserve C.jet_secp_sha_absorb_full C.jet_secp_sha_finalize_short.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition checksig_pad_word : Ty.tySem (Word 9) :=
 @fromZ (WordToZ 9) 0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400.
Definition checksig_hash_word (ir h:Ty.tySem (Word 8)) :=
 @Simplicity.SHA256.hashBlock Alg.CoreFunSem
  (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (checksig_iv_word,(ir,h)),checksig_pad_word).
Lemma checksig_pad_bytes:
 map word8_array_value (vector_values (Word 3) 6 checksig_pad_word)=sha_pad (Int64.repr 128).
Proof. vm_compute;reflexivity. Qed.
Lemma checksig_hash_registers ir h:
 state_regs (checksig_hash_word ir h)=
 SHA256.hash_block (SHA256.hash_block (state_regs checksig_iv_word)
   (be_words (schnorr_word_bytes ir++schnorr_word_bytes h))) (be_words (sha_pad (Int64.repr 128))).
Proof.
 unfold checksig_hash_word;rewrite hashBlock_regs,checksig_pad_bytes,schnorr_hash_pair_registers;reflexivity.
Qed.
Theorem eval_checksig_sha_calls (Model:memcpy_model) (ir h:Ty.tySem (Word 8)) m bc bs bm om:
 bc<>bs ->bc<>bm ->secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 Ptrofs.unsigned om+64<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->
 uint32_array_at m bs 0 (state_regs checksig_iv_word) ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 64)) ->
 Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 schnorr_bytes_at m bm om (schnorr_word_bytes ir++schnorr_word_bytes h) ->exists m1 mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bm om;Vlong (Int64.repr 64)] E0 m1 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m1 (Internal jets_secp.f_sha256_finalize)
  [Vptr bc Ptrofs.zero] E0 mf (Vint Int.one) /\
 uint32_array_at mf bs 0 (state_regs (checksig_hash_word ir h)) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 192)) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros CS CM Startup FC FS Hi Pointer State Counter Overflow Bytes.
 assert (Length:length (schnorr_word_bytes ir++schnorr_word_bytes h)=64%nat)
  by (rewrite app_length,!schnorr_word_bytes_length;reflexivity).
 destruct (eval_secp_sha_absorb_full_counter Model [] (schnorr_word_bytes ir++schnorr_word_bytes h)
  (state_regs checksig_iv_word) 64 m bc bs bm om ltac:(cbn;lia) Length (schnorr_state_regs_length checksig_iv_word)
  ltac:(lia) ltac:(rewrite Length;lia) eq_refl CM CS Startup FC FS
  ltac:(rewrite Length;exact Hi) Pointer State Counter Overflow ltac:(intros i Index;cbn in Index;lia) Bytes)
  as (m1 & Absorb & State1 & Pointer1 & Counter1 & Overflow1 & FC1 & FS1 & Frame1 & Read1 & Start1).
 cbn [app] in State1;rewrite Length in Absorb,Counter1.
 assert (LFirst:length (SHA256.hash_block (state_regs checksig_iv_word)
  (be_words (schnorr_word_bytes ir++schnorr_word_bytes h)))=8%nat).
 { rewrite <-schnorr_hash_pair_registers;apply schnorr_state_regs_length. }
 destruct (eval_secp_sha_finalize_short Model []
  (SHA256.hash_block (state_regs checksig_iv_word) (be_words (schnorr_word_bytes ir++schnorr_word_bytes h)))
  128 m1 bc bs ltac:(cbn;lia) LFirst ltac:(lia) ltac:(cbn;lia) eq_refl CS Start1 FC1 FS1
  Pointer1 State1 Counter1 Overflow1 ltac:(intros i Index;cbn in Index;lia))
  as (mf & Finalize & Result & PointerF & CounterF & OverflowF & FCF & FSF & FrameF & ReadF & StartF).
 exists m1,mf;split;[exact Absorb|];split;[exact Finalize|];split.
 - rewrite checksig_hash_registers;exact Result.
 - split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
   split;[exact FCF|];split;[exact FSF|];split.
   + eapply lframe_trans;[exact Frame1|exact FrameF].
   + split.
     * eapply preserved_trans;[exact Read1|exact ReadF].
     * exact StartF.
Qed.
