(** The three actual challenge-input absorption calls after the tagged prefix.
    The fixed 32-byte public message follows r32 and pubkey32. The canonical
    tag constructor is proved separately; finalization and scalar conversion
    are still required for the complete challenge caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require sha.SHA256.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init
 C.jet_sha_ctx8_model C.jet_secp_linkage C.jet_clight_internal_preserve
 C.jet_secp_sha_startup C.jet_secp_sha_absorb_short C.jet_secp_sha_absorb_full.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition schnorr_bytes_at m b o (bytes:list int) := forall i,
 (i<length bytes)%nat -> Mem.load Mint8unsigned m b (Ptrofs.unsigned o+Z.of_nat i)=
  Some (Vint (nth i bytes Int.zero)).
Lemma schnorr_bytes_valid m b o bytes : (0<length bytes)%nat ->
 schnorr_bytes_at m b o bytes -> Mem.valid_block m b.
Proof.
 intros Length Bytes;pose proof (Mem.load_valid_access _ _ _ _ _ (Bytes 0%nat Length)) as [Perm Align].
 eapply Mem.perm_valid_block;apply (Perm (Ptrofs.unsigned o));change (size_chunk Mint8unsigned) with 1;lia.
Qed.
Lemma schnorr_bytes_framed m mf P b o bytes : lframe P m mf ->
 Mem.valid_block m b -> (forall ofs,P b ofs) ->
 schnorr_bytes_at m b o bytes -> schnorr_bytes_at mf b o bytes.
Proof. intros [Loads _] Old Outside Bytes i Index;rewrite Loads;[apply Bytes;exact Index|exact Old|intros;apply Outside]. Qed.

Theorem eval_schnorr_challenge_absorb (Hmodel:memcpy_model) r pk msg regs m bc bs br bp bm or op om :
 length r=32%nat -> length pk=32%nat -> length msg=32%nat -> length regs=8%nat ->
 bc<>bs -> bc<>br -> bc<>bp -> bc<>bm -> bs<>bm ->
 secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable -> Mem.range_perm m bs 0 32 Cur Freeable ->
 Ptrofs.unsigned or+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned op+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned om+32<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) -> uint32_array_at m bs 0 regs ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 64)) ->
 Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 schnorr_bytes_at m br or r -> schnorr_bytes_at m bp op pk -> schnorr_bytes_at m bm om msg ->
 exists m1 m2 mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr br or;Vlong (Int64.repr 32)] E0 m1 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m1 (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bp op;Vlong (Int64.repr 32)] E0 m2 (Vint Int.one) /\
 Clight2.eval_funcall secp_ge m2 (Internal jets_secp.f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bm om;Vlong (Int64.repr 32)] E0 mf (Vint Int.one) /\
 uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (r++pk))) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 160)) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bc (16+Z.of_nat i)=Some (Vint (nth i msg Int.zero))) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros LR LP LM LRegs CS CR CP CM SM Startup FC FS RHi PHi MHi Pointer State Counter Overflow RBytes PBytes MBytes.
 assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);lia).
 assert (VP:Mem.valid_block m bp) by (eapply schnorr_bytes_valid;[rewrite LP;lia|exact PBytes]).
 assert (VM:Mem.valid_block m bm) by (eapply schnorr_bytes_valid;[rewrite LM;lia|exact MBytes]).
 destruct (eval_secp_sha_absorb_short_counter Hmodel [] r 64 m bc br or
  (Vptr bs Ptrofs.zero) ltac:(cbn [length];rewrite LR;lia) ltac:(lia)
  ltac:(rewrite LR;lia) eq_refl CR Startup FC ltac:(rewrite LR;exact RHi)
  Pointer Counter Overflow ltac:(intros i Index;cbn in Index;lia) RBytes) as
  (m1 & Call1 & Pointer1 & Counter1 & Overflow1 & Buffer1 & FC1 & Frame1 & Readonly1 & Startup1).
 cbn [app] in Counter1,Buffer1;rewrite LR in Call1,Counter1.
 assert (FS1:Mem.range_perm m1 bs 0 32 Cur Freeable).
 { intros ofs Range;apply (proj1 (proj2 Frame1));[exact VS|congruence|apply FS;exact Range]. }
 assert (State1:uint32_array_at m1 bs 0 regs).
 { intros i v Nth;rewrite (proj1 Frame1);[apply State;exact Nth|exact VS|intros;congruence]. }
 assert (PBytes1:schnorr_bytes_at m1 bp op pk).
 { eapply schnorr_bytes_framed;[exact Frame1|exact VP|intros;congruence|exact PBytes]. }
 destruct (eval_secp_sha_absorb_full_counter Hmodel r pk regs 96 m1 bc bs bp op
  ltac:(rewrite LR;lia) ltac:(rewrite LR,LP;reflexivity) LRegs ltac:(lia)
  ltac:(rewrite LP;lia) ltac:(rewrite LR;reflexivity) CP CS Startup1 FC1 FS1
  ltac:(rewrite LP;exact PHi) Pointer1 State1 Counter1 Overflow1 Buffer1 PBytes1) as
  (m2 & Call2 & State2 & Pointer2 & Counter2 & Overflow2 & FC2 & FS2 & Frame2 & Readonly2 & Startup2).
 rewrite LP in Call2,Counter2.
 assert (MBytes2:schnorr_bytes_at m2 bm om msg).
 { eapply schnorr_bytes_framed;[exact Frame2|exact (proj2 (proj2 Frame1) _ VM)|intros;split;congruence|].
   eapply schnorr_bytes_framed;[exact Frame1|exact VM|intros;congruence|exact MBytes]. }
 destruct (eval_secp_sha_absorb_short_counter Hmodel [] msg 128 m2 bc bm om
  (Vptr bs Ptrofs.zero) ltac:(cbn [length];rewrite LM;lia) ltac:(lia)
  ltac:(rewrite LM;lia) eq_refl CM Startup2 FC2 ltac:(rewrite LM;exact MHi)
  Pointer2 Counter2 Overflow2 ltac:(intros i Index;cbn in Index;lia) MBytes2) as
  (mf & Call3 & Pointer3 & Counter3 & Overflow3 & Buffer3 & FC3 & Frame3 & Readonly3 & Startup3).
 cbn [app] in Counter3,Buffer3;rewrite LM in Call3,Counter3.
 assert (VS2:Mem.valid_block m2 bs) by (apply (proj2 (proj2 Frame2)),(proj2 (proj2 Frame1));exact VS).
 exists m1,m2,mf;split;[exact Call1|];split;[exact Call2|];split;[exact Call3|];split.
 - intros i v Nth;rewrite (proj1 Frame3);[apply State2;exact Nth|exact VS2|intros;congruence].
 - split;[exact Pointer3|];split;[exact Counter3|];split;[exact Overflow3|];split.
   + rewrite LM in Buffer3;exact Buffer3.
   + split;[exact FC3|];split.
     * intros ofs Range;apply (proj1 (proj2 Frame3));[exact VS2|congruence|apply FS2;exact Range].
     * split.
       -- eapply lframe_trans;[|eapply lframe_implies;[exact Frame3|intros b ofs [NC NS] Old;exact NC]].
          eapply lframe_trans;[eapply lframe_implies;[exact Frame1|intros b ofs [NC NS] Old;exact NC]|exact Frame2].
       -- split;[eapply preserved_trans;[exact Readonly1|eapply preserved_trans;eassumption]|exact Startup3].
Qed.
