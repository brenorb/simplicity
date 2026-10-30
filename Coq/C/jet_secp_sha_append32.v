(** Compose existing byte-absorption proofs for the two hash-word buffer states. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require sha.SHA256.
Require Import C.jet_sx_mem C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha_ctx8_model
 C.jet_secp_linkage C.jet_secp_sha_startup C.jet_secp_sha_absorb_short C.jet_secp_sha_absorb_full
 C.jet_secp_curve_frame C.jet_clight_internal_preserve.
Require C.jets_secp.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition sha_append32_regs (l regs bytes:list int):=
 if Nat.eqb (length l) 0 then regs else SHA256.hash_block regs (be_words (l++bytes)).
Definition sha_append32_buffer (l bytes:list int):=if Nat.eqb (length l) 0 then l++bytes else [].
Local Opaque secp_ge.
Theorem eval_secp_sha_append32 (Copy:memcpy_model) l bytes regs total m bc bs ba:
 (length l=0%nat \/length l=32%nat) ->length bytes=32%nat ->length regs=8%nat ->
 0<=total ->total+32<2305843009213693952 ->total mod 64=Z.of_nat (length l) ->
 bc<>bs ->bc<>ba ->secp_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
 Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
 Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) ->Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
 (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets_secp.f_sha256_uchars)
 [Vptr bc Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong (Int64.repr 32)] E0 mf (Vint Int.one) /\
 uint32_array_at mf bs 0 (sha_append32_regs l regs bytes) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (total+32))) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 (forall i,(i<length (sha_append32_buffer l bytes))%nat ->Mem.load Mint8unsigned mf bc (16+Z.of_nat i)=
  Some (Vint (nth i (sha_append32_buffer l bytes) Int.zero))) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Used LB LR Nonnegative Bound Remainder CS CA Startup FC FS Pointer State Counter Overflow Buffer Source.
 assert (Fits:Ptrofs.unsigned Ptrofs.zero+Z.of_nat (length bytes)<=Ptrofs.max_unsigned).
 { rewrite Ptrofs.unsigned_zero,LB;clear;change (0+32<=18446744073709551615);lia. }
 assert (Bytes:forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned Ptrofs.zero+Z.of_nat i)=
  Some (Vint (nth i bytes Int.zero))) by (rewrite Ptrofs.unsigned_zero;exact Source).
 destruct Used as [Empty|Full].
 - destruct (eval_secp_sha_absorb_short_counter Copy l bytes total m bc ba Ptrofs.zero (Vptr bs Ptrofs.zero)
   ltac:(rewrite Empty,LB;lia) Nonnegative ltac:(rewrite LB;exact Bound) Remainder CA Startup FC Fits Pointer Counter Overflow Buffer Bytes)
   as (mf & Call & PointerF & CounterF & OverflowF & BufferF & FCF & Frame & ReadF & StartF).
   rewrite LB in Call,CounterF.
   assert (FSF:Mem.range_perm mf bs 0 32 Cur Freeable).
   { eapply curve_keep_free;[clear;lia|exact FS|exact Frame|intros;clear -CS;congruence]. }
   assert (StateF:uint32_array_at mf bs 0 regs).
   { intros i v Nth;rewrite (proj1 Frame Mint32 bs (0+4*Z.of_nat i));[apply State;exact Nth| |intros;clear -CS;congruence].
     eapply Mem.perm_valid_block;apply (FS 0);clear;lia. }
   exists mf;split;[exact Call|];unfold sha_append32_regs,sha_append32_buffer;rewrite Empty;
   split;[exact StateF|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];
   split;[exact BufferF|];split;[exact FCF|];split;[exact FSF|];split.
   + eapply lframe_implies;[exact Frame|intros b pos [NC NS] Old;exact NC].
   + split;assumption.
 - destruct (eval_secp_sha_absorb_full_counter Copy l bytes regs total m bc bs ba Ptrofs.zero
   ltac:(rewrite Full;lia) ltac:(rewrite Full,LB;reflexivity) LR Nonnegative ltac:(rewrite LB;exact Bound)
   Remainder CA CS Startup FC FS Fits Pointer State Counter Overflow Buffer Bytes)
   as (mf & Call & StateF & PointerF & CounterF & OverflowF & FCF & FSF & Frame & ReadF & StartF).
   rewrite LB in Call,CounterF.
   exists mf;split;[exact Call|];unfold sha_append32_regs,sha_append32_buffer;rewrite Full;
   split;[exact StateF|];split;[exact PointerF|];split;[exact CounterF|];split;[exact OverflowF|];split.
   + intros i Index;cbn in Index;lia.
   + split;[exact FCF|];split;[exact FSF|];split;[exact Frame|];split;assumption.
Qed.
