(** Faithful challenge subprogram of frozen LibSecp256k1.bip_0340_check:
    input ((public key, message), (r, s)); m, iv, and e at lines 703--706.
    The whole signature predicate and its C execution remain separate. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Integers Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.SHA256.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_canonical_parametric
 C.jet_secp_schnorr_tagged_spec C.jet_secp_schnorr_challenge_hash
 C.jet_secp_schnorr_challenge_function C.jet_secp_schnorr_challenge_absorb
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage C.jet_secp_sha_startup C.jet_clight_internal_preserve.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Definition literal_bip0340_args:=Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8)).
Definition literal_bip0340_challenge_message {term:Alg.Core.Algebra} :
 term literal_bip0340_args (Ty.Prod (Word 9) (Word 9)) :=
 (I (O H) &&& O (O H)) &&& (O (I H) &&& Alg.scribe schnorr_challenge_pad_word).
Definition literal_bip0340_challenge {term:Alg.Core.Algebra} : term literal_bip0340_args (Word 8) :=
 @literal_bip0340_challenge_message term >>>
 (((Alg.scribe schnorr_challenge_iv_word &&& O H) >>> @Simplicity.SHA256.hashBlock term) &&& I H)
 >>> @Simplicity.SHA256.hashBlock term >>> @canonical_scalar_normalize term.
Lemma literal_bip0340_challenge_parametric:Alg.Core.Parametric (@literal_bip0340_challenge).
Proof.
 intros a b R;unfold literal_bip0340_challenge,literal_bip0340_challenge_message.
 repeat first [apply Simplicity.SHA256.hashBlock_Parametric|apply canonical_scalar_normalize_parametric|
 apply Alg.scribe_Parametric|apply Alg.comp_Parametric|apply Alg.pair_Parametric|
 apply Alg.take_Parametric|apply Alg.drop_Parametric|apply Alg.iden_Parametric].
Qed.
Local Opaque Simplicity.SHA256.hashBlock canonical_scalar_normalize schnorr_challenge_iv_word schnorr_challenge_pad_word.
Lemma literal_bip0340_challenge_value (pk msg r s:Ty.tySem (Word 8)):
 @literal_bip0340_challenge Alg.CoreFunSem ((pk,msg),(r,s))=
 @canonical_scalar_normalize Alg.CoreFunSem (schnorr_challenge_hash_word r pk msg).
Proof.
 unfold literal_bip0340_challenge,literal_bip0340_challenge_message,schnorr_challenge_hash_word.
 cbn -[Simplicity.SHA256.hashBlock canonical_scalar_normalize Alg.scribe schnorr_challenge_iv_word schnorr_challenge_pad_word].
 rewrite !Alg.scribe_correct;reflexivity.
Qed.
Theorem eval_schnorr_challenge_literal (Model:memcpy_model)
 (pk msg r s:Ty.tySem (Word 8)) m be ba oa bm om bp op:
 secp_sha_startup m ->Mem.range_perm m be 0 32 Cur Freeable ->
 Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->Ptrofs.unsigned op+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned om+32<=Ptrofs.max_unsigned ->
 schnorr_bytes_at m ba oa (schnorr_word_bytes r) ->
 schnorr_bytes_at m bp op (schnorr_word_bytes pk) ->
 schnorr_bytes_at m bm om (schnorr_word_bytes msg) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_secp256k1_schnorrsig_challenge)
 [Vptr be Ptrofs.zero;Vptr ba oa;Vptr bm om;Vlong (Int64.repr 32);Vptr bp op] E0 mf Vundef /\
 scalar_at mf be 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@literal_bip0340_challenge Alg.CoreFunSem ((pk,msg),(r,s)))))) /\
 Mem.range_perm mf be 0 32 Cur Freeable /\lframe (fun b _=>b<>be) m mf /\
 readonly_preserved m mf /\secp_sha_startup mf.
Proof. rewrite literal_bip0340_challenge_value;apply eval_schnorr_challenge_word;exact Model. Qed.
