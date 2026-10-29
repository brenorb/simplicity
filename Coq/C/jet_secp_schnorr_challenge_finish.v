(** The two original calls that serialize a digest and normalize its scalar.
    These close the post-hash data path; the full challenge caller still needs
    its constructor-slot copy, statement spine and private-local release. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_sha_ctx8_model C.jet_sha_word_bytes
 C.jet_uint32_array_init C.jet_secp_linkage C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_sha_owned C.jet_secp_scalar_set_bytes C.jet_secp_scalar_set_storage C.jet_secp_scalar_set_shape
 C.jet_secp_scalar_overflow_numeric C.jet_secp_canonical_scalar C.jet_secp_b32_exec C.jet_secp_fe_math.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition schnorr_digest_scalar_limbs (h:Ty.tySem (Word 8)) be bb :=
 scalar_set_limb (byte_rho (secp_sha_digest_bytes (state_regs h))) (lay [(be,0);(bb,0)]).
Lemma schnorr_digest_scalar_value h be bb :
 scalar_limb_value (schnorr_digest_scalar_limbs h be bb)=
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem h).
Proof.
 unfold schnorr_digest_scalar_limbs;rewrite scalar_set_bytes_mod_group.
 - rewrite canonical_scalar_normalize_numeric;unfold secp_sha_digest_bytes.
   rewrite sha_state_bytes_integer;reflexivity.
 - apply secp_sha_digest_length;unfold state_regs;rewrite <-hash256_reg_chunks;apply Digest.hash256_len.
 - apply secp_sha_digest_bounds.
Qed.
Theorem eval_schnorr_challenge_finish h m be bb bs :
 be<>bb ->bb<>bs ->uint32_array_at m bs 0 (state_regs h) ->
 Mem.range_perm m be 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
 Mem.range_perm m bs 0 32 Cur Freeable ->exists mi mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_fromMidstate)
  [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mi Vundef /\
 Clight2.eval_funcall secp_ge mi (Internal jets_secp.f_secp256k1_scalar_set_b32)
  [Vptr be Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
 (forall i,(i<4)%nat ->Mem.load Mint64 mf be (8*Z.of_nat i)=
   Some (Vlong (schnorr_digest_scalar_limbs h be bb i))) /\
 scalar_limb_value (schnorr_digest_scalar_limbs h be bb)=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem h) /\
 Mem.range_perm mf be 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>be /\b<>bb) m mf /\readonly_preserved m mf.
Proof.
 intros EB BS State FE FB FS.
 assert (LR:length (state_regs h)=8%nat).
 { unfold state_regs;rewrite <-hash256_reg_chunks;apply Digest.hash256_len. }
 assert (VE:Mem.valid_block m be) by (eapply Mem.perm_valid_block;apply (FE 0);lia).
 destruct (eval_secp_sha_digest_owned (state_regs h) m bb bs LR BS State FB FS) as
  (mi & Serialize & Bytes & StateI & FBI & FSI & FrameI & ReadonlyI).
 assert (FEI:Mem.range_perm mi be 0 32 Cur Freeable).
 { intros ofs Range;apply (proj1 (proj2 FrameI));[exact VE|exact EB|apply FE;exact Range]. }
 destruct (eval_scalar_set_b32_storage (secp_sha_digest_bytes (state_regs h)) be bb 0 mi
  (secp_sha_digest_length _ LR) (secp_sha_digest_bounds _) EB ltac:(lia)
  ltac:(change (32<=18446744073709551615);lia) FEI
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply FBI;exact Range|constructor]) Bytes) as
  (mf & Parse & Limbs & Value & Perm & FrameF & ReadonlyF).
 exists mi,mf;split;[exact Serialize|];split;[exact Parse|];split;[exact Limbs|];split.
 - apply schnorr_digest_scalar_value.
 - split;[intros ofs Range;apply Perm,FEI;exact Range|];split;
   [intros ofs Range;apply Perm,FBI;exact Range|];split;
   [intros ofs Range;apply Perm,FSI;exact Range|];split.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact FrameI|].
       intros b ofs [OtherScalar OtherBytes] Old;exact OtherBytes.
     * exact FrameF.
   + eapply preserved_trans;[exact ReadonlyI|exact ReadonlyF].
Qed.
