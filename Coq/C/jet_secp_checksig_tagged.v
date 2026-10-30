(** Original tagged initializer instantiated with the frozen Signature global. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Clight ClightBigstep Ctypes Values Events.
Require Import C.jet_secp_checksig_tag C.jet_secp_tagged_init C.jet_memcpy_model
 C.jet_secp_linkage C.jet_secp_schnorr_startup C.jet_sha_ctx8_model C.jet_uint32_array_init
 C.jet_sx_mem C.jet_clight_internal_preserve C.jet_clight_forward Simplicity.Word.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge checksig_tag_block.
Lemma checksig_iv_state_regs:state_regs checksig_iv_word=checksig_iv_words.
Proof.
 unfold state_regs;rewrite checksig_iv_registers,<-hash256_reg_chunks.
 unfold checksig_iv_word;rewrite Word.to_from_hash256;reflexivity.
Qed.
Lemma checksig_tag_separate m b hi:checksig_tag_ok m ->0<hi ->Mem.range_perm m b 0 hi Cur Freeable ->b<>checksig_tag_block.
Proof.
 intros [_ [_ NoWrite]] Positive Free Same;subst b.
 apply (NoWrite 0);apply Mem.perm_cur_max;eapply Mem.perm_implies;[apply Free;lia|constructor].
Qed.
Theorem checksig_startup_owned_forward m mf (slots:list (block*Z)):
 checksig_startup m ->mem_forward m mf ->
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe (fun b _=>~In b (map fst slots)) m mf ->checksig_startup mf.
Proof.
 intros [Schnorr Tag] Forward Owned Frame;split.
 - eapply schnorr_startup_owned_forward;[exact Schnorr|exact Forward|exact Owned|exact Frame].
 - eapply checksig_tag_framed;[exact Tag|exact Forward|exact Frame|].
   intros pos Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b.
   destruct (Owned _ hi Slot) as [Positive Free].
   exact (checksig_tag_separate m checksig_tag_block hi Tag Positive Free eq_refl).
Qed.
Theorem eval_checksig_tagged_init (Model:memcpy_model) m bc bs:
 bc<>bs ->checksig_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_tagged_init)
  [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr checksig_tag_block Ptrofs.zero] E0 mf Vundef /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 uint32_array_at mf bs 0 (state_regs checksig_iv_word) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\checksig_startup mf.
Proof.
 intros Separate Ready FC FS;pose proof (proj2 Ready) as Tag.
 destruct Tag as (Words & Readable & NoWrite).
 destruct (eval_tagged_sha_init_owned Model checksig_iv_words m bc bs checksig_tag_block
  eq_refl (checksig_tag_separate m bs 32 (proj2 Ready) ltac:(lia) FS) Separate FC FS Readable Words)
  as (mf & Call & Pointer & Counter & Overflow & State & FCF & FSF & Frame & Readonly).
 exists mf;split;[exact Call|];split;[exact Pointer|];split;[exact Counter|];split;[exact Overflow|];split.
 - rewrite checksig_iv_state_regs;exact State.
 - split;[exact FCF|];split;[exact FSF|];split;[exact Frame|];split;[exact Readonly|].
   eapply checksig_startup_owned_forward with (slots:=[(bc,88);(bs,32)]);
    [exact Ready|exact (proj1 Readonly)| |].
   + intros b hi Member;cbn [In] in Member.
     destruct Member as [SlotC|Rest].
     * inversion SlotC;subst;split;[lia|exact FC].
     * destruct Rest as [SlotS|Empty].
       -- inversion SlotS;subst;split;[lia|exact FS].
       -- contradiction.
   + eapply lframe_implies;[exact Frame|].
     intros b pos Outside Old;cbn [map fst In] in Outside;split;intuition congruence.
Qed.
