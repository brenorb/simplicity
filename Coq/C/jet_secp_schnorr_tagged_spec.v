(** Canonical BIP0340/challenge tag and its original C initializer.
    Closed SHA computation is compared by unsigned words, then exact integer
    representation is recovered with repr_unsigned (no proof-irrelevance axiom). *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers.
Require Import Simplicity.Digest Simplicity.Word C.jet_secp_schnorr_tagged_init
 C.jet_sha_ctx8_model C.jet_uint32_array_init C.jet_secp_linkage C.jet_sx_mem
 C.jet_clight_internal_preserve.
From compcert Require Import AST Memory ClightBigstep Ctypes Values Events.
Require C.jets_secp.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_challenge_tag_digest := Digest.stringHash "BIP0340/challenge".
Definition schnorr_challenge_tag_iv := Digest.compress Digest.sha256_iv schnorr_challenge_tag_digest schnorr_challenge_tag_digest.
Lemma schnorr_tag_iv_registers : schnorr_tagged_words = Digest.hash256_reg schnorr_challenge_tag_iv.
Proof.
  assert (Words: map Int.unsigned schnorr_tagged_words =
    map Int.unsigned (Digest.hash256_reg schnorr_challenge_tag_iv)).
  { vm_compute;reflexivity. }
  assert (Recover: forall xs:list Int.int,
    map Int.repr (map Int.unsigned xs)=xs).
  { intro xs;induction xs as [|x xs IH];cbn;[reflexivity|].
    rewrite Int.repr_unsigned, IH;reflexivity. }
  rewrite <- (Recover schnorr_tagged_words),
    <- (Recover (Digest.hash256_reg schnorr_challenge_tag_iv));now rewrite Words.
Qed.

Definition schnorr_challenge_iv_word := Word.from_hash256 schnorr_challenge_tag_iv.
Lemma schnorr_challenge_iv_state_regs : state_regs schnorr_challenge_iv_word = schnorr_tagged_words.
Proof.
 unfold state_regs;symmetry;rewrite schnorr_tag_iv_registers.
 rewrite <- hash256_reg_chunks;unfold schnorr_challenge_iv_word.
 now rewrite Word.to_from_hash256.
Qed.

(** The full original constructor now establishes the canonical tag midstate.
    Counter 64 records the consumed tagged-prefix block, not an empty hash. *)
Theorem eval_schnorr_tagged_init_canonical m bc bs : bc<>bs ->
  Mem.range_perm m bc 0 88 Cur Freeable -> Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_schnorrsig_sha256_tagged)
    [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  uint32_array_at mf bs 0 (state_regs schnorr_challenge_iv_word) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\ Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\ b<>bs) m mf /\ readonly_preserved m mf.
Proof. rewrite schnorr_challenge_iv_state_regs;apply eval_schnorr_tagged_init_owned. Qed.

