(** Complete original sha256_uchars call when this input fills one block.
    Shared setup, checked loop, zero-length tail, entry/return and local free
    are composed; the existing bounded memcpy condition remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require sha.SHA256.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init C.jet_sha_ctx8_model
  C.jet_secp_linkage C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec
  C.jet_secp_sha_context C.jet_secp_sha_startup C.jet_secp_sha_absorb_head
  C.jet_secp_sha_absorb_short C.jet_secp_sha_absorb_block C.jet_secp_statement_prefix
  C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_globals C.jet_elements_taptweak_context
 C.jet_elements_taptweak_absorb_head C.jet_elements_taptweak_absorb_short C.jet_elements_taptweak_absorb_block.
Local Opaque elements_taptweak_ge.
Theorem eval_elements_taptweak_sha_absorb_full_counter (Hmodel:memcpy_model) l bytes regs total m bc bs ba oa :
  (length l<64)%nat ->(length l+length bytes=64)%nat ->length regs=8%nat ->
  0<=total -> total+Z.of_nat (length bytes)<2305843009213693952 ->
  total mod 64=Z.of_nat (length l) ->
  bc<>ba ->bc<>bs ->elements_taptweak_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Ptrofs.unsigned oa+Z.of_nat (length bytes)<=Ptrofs.max_unsigned ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i bytes Int.zero))) ->exists mf,
  Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_uchars)
    [Vptr bc Ptrofs.zero;Vptr ba oa;Vlong (Int64.repr (Z.of_nat (length bytes)))] E0 mf (Vint Int.one) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++bytes))) /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (total+Z.of_nat (length bytes)))) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\elements_taptweak_sha_startup mf.
Proof.
  intros Used Full LR Nonnegative Total Remainder CA CS Startup FC FS SourceHi Pointer State Counter Overflow Buffer Source.
  destruct (exec_elements_taptweak_sha_absorb_head_counter (length l) (length bytes) total m bc ba oa Used
    Nonnegative Total Remainder Startup FC Counter Overflow) as
    (leh & mh & Head & HC & HA & HN & HD & HB & CounterH & OverflowH & FCH & LoadsH & BufferH & PermH & FrameH & ReadonlyH & StartupH).
  assert (PointerH:Mem.load Mptr mh bc 0=Some (Vptr bs Ptrofs.zero)).
  { rewrite LoadsH by (right;left;reflexivity);exact Pointer. }
  destruct (exec_elements_taptweak_sha_fill_block Hmodel l bytes regs leh mh bc bs ba oa Used Full LR CA CS StartupH FCH
    ltac:(intros pos Range;apply PermH,FS;exact Range) SourceHi HC HA HB) as
    (lel & mf & Loop & CtxL & LenL & DeltaL & BlockL & Output & FCF & FSF & Fields & FrameL & ReadonlyL & StartupF).
  { replace (Z.of_nat (length bytes)) with (64-Z.of_nat (length l)) by lia;exact HD. }
  { exact HN. }
  { exact PointerH. }
  { intros i v Nth;rewrite LoadsH by (left;congruence);apply State;exact Nth. }
  { intros i Index;rewrite BufferH by (change (size_chunk Mint8unsigned) with 1;lia);apply Buffer;exact Index. }
  { intros i Index;rewrite LoadsH by (left;congruence);apply Source;exact Index. }
  assert (OverflowF:Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero)).
  { rewrite Fields by (right;lia);exact OverflowH. }
  set (lef:=PTree.set jets_sha._t'2 (Vint Int.zero) lel).
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env)
      (le1:=uc_le0 bc 0 ba oa (Int64.repr (Z.of_nat (length bytes)))) (m1:=m)
      (le2:=lef) (m2:=mf) (out:=Out_return (Some (Vint Int.one,tint))).
    + apply elements_taptweak_sha_uchars_entry.
    + rewrite elements_taptweak_sha_absorb_body;eapply exec_statement_prefix_then_last;[exact Head|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|].
      unfold uc_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lel) (m1:=mf).
      * eapply exec_Sifthenelse with (b:=false);[apply eval_Etempvar;exact LenL|reflexivity|constructor].
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lef) (m1:=mf).
        -- apply exec_Sset;eapply (eval_elements_taptweak_ctx_field SOverflow) with (chunk:=Mint8unsigned) (base:=0);
             [lia|change (88<=18446744073709551615);lia|reflexivity|rewrite CtxL;exact HC|exact OverflowF].
        -- apply exec_Sreturn_some;eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
    + cbn;split;[discriminate|reflexivity].
    + reflexivity.
  - split;[exact Output|];split.
    + rewrite Fields by (left;change (size_chunk Mptr) with 8;lia);exact PointerH.
    + split.
      * rewrite Fields by (left;reflexivity);exact CounterH.
      * split;[exact OverflowF|];split;[exact FCF|];split;[exact FSF|];split.
        -- eapply lframe_trans;[eapply lframe_implies;[exact FrameH|intros b pos [NC NS] Old;exact NC]|exact FrameL].
        -- split;[eapply preserved_trans;eassumption|exact StartupF].
Qed.

Theorem eval_elements_taptweak_sha_absorb_full (Hmodel:memcpy_model) l bytes regs m bc bs ba oa :
  (length l<64)%nat ->(length l+length bytes=64)%nat ->length regs=8%nat ->
  bc<>ba ->bc<>bs ->elements_taptweak_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Ptrofs.unsigned oa+Z.of_nat (length bytes)<=Ptrofs.max_unsigned ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr (Z.of_nat (length l)))) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  (forall i,(i<length bytes)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i bytes Int.zero))) ->exists mf,
  Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_uchars)
    [Vptr bc Ptrofs.zero;Vptr ba oa;Vlong (Int64.repr (Z.of_nat (length bytes)))] E0 mf (Vint Int.one) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++bytes))) /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\elements_taptweak_sha_startup mf.
Proof.
 intros Used Full LR CA CS Startup FC FS SourceHi Pointer State Counter Overflow Buffer Source.
 replace (Int64.repr 64) with
   (Int64.repr (Z.of_nat (length l)+Z.of_nat (length bytes))) by (f_equal;lia).
 eapply eval_elements_taptweak_sha_absorb_full_counter;try eassumption.
 - lia.
 - lia.
 - apply Z.mod_small;lia.
Qed.
