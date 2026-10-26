(** Actual SHA initialization and state-to-byte serialization in the secp
    program, reusing the checked core/SHA calls through validated transport. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_sha_linkage C.jet_secp_linkage
  C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha256_init_layout
  C.jet_sha_be32_write C.jet_sha_hash_exec C.jet_secp_sha_pure_transport
  C.jet_secp_local_regions C.jet_clight_internal_preserve.
Require C.jets C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque ge0 sha_ge secp_ge.

Theorem eval_secp_sha_init_owned m bc bs : bc<>bs ->
  Mem.range_perm m bc 0 88 Cur Freeable -> Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_init)
    [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong Int64.zero) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  uint32_array_at mf bs 0 sha256_iv_words /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\ Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\ b<>bs) m mf /\ readonly_preserved m mf.
Proof.
  intros Separate FC FS.
  destruct (eval_sha256_init_layout m bc bs 0 Separate ltac:(lia)
    ltac:(change (32<=18446744073709551615);lia) ltac:(exists 0;reflexivity)
    (freeable_range_writable _ _ _ _ FC) (freeable_range_writable _ _ _ _ FS))
    as (mf & Init & Pointer & Counter & Overflow & State & Loads & Perm & Valid).
  pose proof (secp_sha_transport_call ge0 jets_sha._sha256_init jets_sha.f_sha256_init m
    [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef
    (or_introl eq_refl) ltac:(right;left;reflexivity) Init) as Call.
  exists mf;split;[exact Call|];split;[exact Pointer|];split;[exact Counter|];split;[exact Overflow|];
    split;[exact State|];split;[intros pos Range;apply Perm,FC;exact Range|];
    split;[intros pos Range;apply Perm,FS;exact Range|];split.
  - split.
    + intros chunk b ofs Old Outside;apply Loads;[exact Old| |];
        [left;pose proof (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as [NC NS];exact NC|
         left;pose proof (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as [NC NS];exact NS].
    + split;[intros;apply Perm;assumption|exact Valid].
  - eapply secp_sha_pure_preserved;[right;left;reflexivity|exact Call].
Qed.

Definition secp_sha_digest_bytes regs := map Int.unsigned (C.jet_sha_be32_write.be_bytes regs).
Lemma secp_sha_zero_ext_byte x : 0<=Int.unsigned (Int.zero_ext 8 x)<=255.
Proof.
  pose proof (Int.zero_ext_range 8 x ltac:(change (0<=8<32);lia)) as Range.
  change (0<=Int.unsigned (Int.zero_ext 8 x)<256) in Range;lia.
Qed.
Lemma secp_sha_digest_length regs : length regs=8%nat -> length (secp_sha_digest_bytes regs)=32%nat.
Proof. intro Len;unfold secp_sha_digest_bytes;rewrite map_length,be_bytes_length,Len;reflexivity. Qed.
Lemma secp_sha_digest_bounds regs : Forall (fun byte=>0<=byte<=255) (secp_sha_digest_bytes regs).
Proof.
  induction regs as [|word rest IH];[constructor|].
  change (Forall (fun byte=>0<=byte<=255)
    (map Int.unsigned (c_be32_bytes (Int64.repr (Int.unsigned word)))++secp_sha_digest_bytes rest)).
  apply Forall_app;split;[unfold c_be32_bytes;cbn [map];repeat constructor;apply secp_sha_zero_ext_byte|exact IH].
Qed.

Theorem eval_secp_sha_digest_owned regs m bb bs : length regs=8%nat -> bb<>bs ->
  uint32_array_at m bs 0 regs ->
  Mem.range_perm m bb 0 32 Cur Freeable -> Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_fromMidstate)
    [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned mf bb (Z.of_nat i)=
    Some (Vint (Int.repr (nth i (secp_sha_digest_bytes regs) 0)))) /\
  uint32_array_at mf bs 0 regs /\
  Mem.range_perm mf bb 0 32 Cur Freeable /\ Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bb) m mf /\ readonly_preserved m mf.
Proof.
  intros Len Separate State FB FS.
  destruct (eval_sha_fromMidstate m bb Ptrofs.zero bs Ptrofs.zero regs Separate Len
    ltac:(change (32<=18446744073709551615);lia) ltac:(change (32<=18446744073709551615);lia)
    ltac:(intros i Index;apply State;apply nth_error_nth';rewrite Len;exact Index)
    (freeable_range_writable _ _ _ _ FB)) as (mf & Write & Bytes & Loads & Perm & Valid).
  pose proof (secp_sha_transport_call sha_ge jets_sha._sha256_fromMidstate jets_sha.f_sha256_fromMidstate m
    [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef
    (or_intror eq_refl) ltac:(do 5 right;left;reflexivity) Write) as Call.
  exists mf;split;[exact Call|];split.
  - intros i Index.
    change (Mem.load Mint8unsigned mf bb (Z.of_nat i)=
      Some (Vint (Int.repr (nth i (map Int.unsigned (C.jet_sha_be32_write.be_bytes regs)) (Int.unsigned Int.zero))))).
    rewrite map_nth,Int.repr_unsigned;apply Bytes;exact Index.
  - split.
    + intros i value Nth;rewrite Loads by (left;congruence);apply State;exact Nth.
    + split;[intros pos Range;apply Perm,FB;exact Range|];
        split;[intros pos Range;apply Perm,FS;exact Range|];split.
      * split.
        -- intros chunk b ofs Old Outside;apply Loads;left.
           apply (Outside ofs);pose proof (size_chunk_pos chunk);lia.
        -- split;[intros;apply Perm;assumption|exact Valid].
      * eapply secp_sha_pure_preserved;[do 5 right;left;reflexivity|exact Call].
Qed.
