(** All original challenge statements from owned local storage. The outer
    function theorem must supply this storage by its actual four allocations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_uint32_array_init C.jet_sha_ctx8_model
 C.jet_secp_linkage C.jet_clight_internal_preserve C.jet_memcpy_model
 C.jet_secp_sha_startup C.jet_secp_schnorr_tagged_spec C.jet_secp_schnorr_challenge_copy
 C.jet_secp_schnorr_challenge_entry C.jet_secp_schnorr_challenge_body
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb
 C.jet_secp_schnorr_challenge_sha C.jet_secp_schnorr_challenge_finish
 C.jet_secp_scalar_overflow_numeric.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma schnorr_owner_framed m mf P b hi:0<hi ->lframe P m mf ->
 (forall ofs,P b ofs) ->Mem.range_perm m b 0 hi Cur Freeable ->Mem.range_perm mf b 0 hi Cur Freeable.
Proof.
 intros Positive Frame Outside Owned pos Range;apply (proj1 (proj2 Frame)).
 - eapply Mem.perm_valid_block;apply (Owned 0);lia.
 - apply Outside.
 - apply Owned;exact Range.
Qed.
Definition schnorr_challenge_storage (bb bs bc br be:block):= [(bb,32);(bs,32);(bc,88);(br,88);(be,32)].
Local Ltac schnorr_distinct Sep:=clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence.
Theorem exec_schnorr_challenge_owned (Model:memcpy_model)
 (r pk msg:Ty.tySem (Word 8)) m bb bs bc br be ba oa bm om bp op:
 NoDup [bb;bs;bc;br;be] ->
 (forall b,In b [ba;bp;bm] ->~In b [bb;bs;bc;br]) ->
 (forall b hi,In (b,hi) (schnorr_challenge_storage bb bs bc br be) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 secp_sha_startup m ->
 Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->Ptrofs.unsigned op+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned om+32<=Ptrofs.max_unsigned ->
 schnorr_bytes_at m ba oa (schnorr_word_bytes r) ->
 schnorr_bytes_at m bp op (schnorr_word_bytes pk) ->
 schnorr_bytes_at m bm om (schnorr_word_bytes msg) ->exists mf,
 Clight2.exec_stmt secp_ge (schnorr_challenge_env bb bs bc br)
 (schnorr_challenge_temps be ba oa bm om bp op) m
 (fn_body jets_secp.f_secp256k1_schnorrsig_challenge) E0
 (schnorr_challenge_temps be ba oa bm om bp op) mf Out_normal /\
 (forall i,(i<4)%nat ->Mem.load Mint64 mf be (8*Z.of_nat i)=
  Some (Vlong (schnorr_digest_scalar_limbs (schnorr_challenge_hash_word r pk msg) be bb i))) /\
 scalar_limb_value (schnorr_digest_scalar_limbs (schnorr_challenge_hash_word r pk msg) be bb)=
  @toZ (WordToZ 8) (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem
    (schnorr_challenge_hash_word r pk msg)) /\
 (forall b hi,In (b,hi) (schnorr_challenge_storage bb bs bc br be) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b [bb;bs;bc;br;be]) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Separate Sources Owned Ready HiA HiP HiM BytesA BytesP BytesM.
 assert (FB:Mem.range_perm m bb 0 32 Cur Freeable) by (apply Owned;unfold schnorr_challenge_storage;cbn [In];tauto).
 assert (FS:Mem.range_perm m bs 0 32 Cur Freeable) by (apply Owned;unfold schnorr_challenge_storage;cbn [In];tauto).
 assert (FC:Mem.range_perm m bc 0 88 Cur Freeable) by (apply Owned;unfold schnorr_challenge_storage;cbn [In];tauto).
 assert (FR:Mem.range_perm m br 0 88 Cur Freeable) by (apply Owned;unfold schnorr_challenge_storage;cbn [In];tauto).
 destruct (eval_schnorr_tagged_init_canonical m br bs ltac:(schnorr_distinct Separate) FR FS) as
 (mt & Tag & PointerT & CounterT & OverflowT & StateT & FRT & FST & FrameT & ReadT).
 assert (FCT:Mem.range_perm mt bc 0 88 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameT|intros;split;schnorr_distinct Separate|exact FC]. }
 destruct (exec_schnorr_challenge_copy (schnorr_challenge_env bb bs bc br)
  (schnorr_challenge_temps be ba oa bm om bp op) mt bc br (Vptr bs Ptrofs.zero)
  (Int64.repr 64) Int.zero eq_refl eq_refl ltac:(schnorr_distinct Separate) FCT FRT
  PointerT CounterT OverflowT) as
 (mc & Copy & PointerC & CounterC & OverflowC & FCC & FRC & FrameC & ReadC).
 assert (StateC:uint32_array_at mc bs 0 (state_regs schnorr_challenge_iv_word)).
 { intros i v Nth;rewrite (proj1 FrameC).
   - apply StateT;exact Nth.
   - eapply Mem.perm_valid_block;apply (FST 0);lia.
   - intros;schnorr_distinct Separate. }
 assert (FSC:Mem.range_perm mc bs 0 32 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameC|intros;schnorr_distinct Separate|exact FST]. }
 assert (FrameI:lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mc).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameT|intros b ofs [R [C S]] Old;split;assumption].
   - eapply lframe_implies;[exact FrameC|intros b ofs [R [C S]] Old;exact C]. }
 assert (ReadI:readonly_preserved m mc) by (eapply preserved_trans;[exact ReadT|exact ReadC]).
 assert (ReadyC:secp_sha_startup mc).
 { eapply secp_sha_startup_preserved;[exact Ready|exact ReadI|exact FrameI|].
   pose proof (proj1 (secp_sha_startup_separate m br 88 Ready ltac:(lia) FR)) as R.
   pose proof (proj1 (secp_sha_startup_separate m bc 88 Ready ltac:(lia) FC)) as C.
   pose proof (proj1 (secp_sha_startup_separate m bs 32 Ready ltac:(lia) FS)) as S.
   intros;repeat split;congruence. }
 assert (InputOutside:forall b,In b [ba;bp;bm] ->b<>br /\b<>bc /\b<>bs).
 { intros b Input;pose proof (Sources b Input) as Safe;cbn [In] in Safe;intuition congruence. }
 destruct (eval_schnorr_challenge_sha_calls Model r pk msg mc bc bs ba bp bm oa op om
  ltac:(schnorr_distinct Separate)
  ltac:(pose proof (InputOutside ba (or_introl eq_refl));intuition congruence)
  ltac:(pose proof (InputOutside bp (or_intror (or_introl eq_refl)));intuition congruence)
  ltac:(pose proof (InputOutside bm (or_intror (or_intror (or_introl eq_refl))));intuition congruence)
  ltac:(pose proof (InputOutside bm (or_intror (or_intror (or_introl eq_refl))));intuition congruence)
  ReadyC FCC FSC HiA HiP HiM PointerC StateC CounterC OverflowC) as
 (m1 & m2 & m3 & mh & RCall & PCall & MCall & Final & StateH & PointerH & CounterH & OverflowH & FCH & FSH & FrameH & ReadH & ReadyH).
 - eapply schnorr_bytes_framed;[exact FrameI| |intros;apply InputOutside;left;reflexivity|exact BytesA].
   eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesA].
 - eapply schnorr_bytes_framed;[exact FrameI| |intros;apply InputOutside;right;left;reflexivity|exact BytesP].
   eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesP].
 - eapply schnorr_bytes_framed;[exact FrameI| |intros;apply InputOutside;right;right;left;reflexivity|exact BytesM].
   eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesM].
 - assert (FrameIH:lframe (fun b _=>b<>br /\b<>bc /\b<>bs) m mh).
   { eapply lframe_trans;[exact FrameI|].
     eapply lframe_implies;[exact FrameH|intros b ofs [R [C S]] Old;split;assumption]. }
   assert (FBH:Mem.range_perm mh bb 0 32 Cur Freeable).
   { eapply schnorr_owner_framed;[lia|exact FrameIH|intros;repeat split;schnorr_distinct Separate|exact FB]. }
   assert (FEH:Mem.range_perm mh be 0 32 Cur Freeable).
   { eapply schnorr_owner_framed;[lia|exact FrameIH|intros;repeat split;schnorr_distinct Separate|].
     apply Owned;unfold schnorr_challenge_storage;cbn [In];tauto. }
   assert (FRH:Mem.range_perm mh br 0 88 Cur Freeable).
   { eapply schnorr_owner_framed;[lia|exact FrameH|intros;split;schnorr_distinct Separate|exact FRC]. }
   destruct (eval_schnorr_challenge_finish (schnorr_challenge_hash_word r pk msg) mh be bb bs
    ltac:(schnorr_distinct Separate) ltac:(schnorr_distinct Separate) StateH FEH FBH FSH) as
    (md & mf & Digest & Scalar & Limbs & Value & FEF & FBF & FSF & FrameF & ReadF).
   assert (FCF:Mem.range_perm mf bc 0 88 Cur Freeable).
   { eapply schnorr_owner_framed;[lia|exact FrameF|intros;split;schnorr_distinct Separate|exact FCH]. }
   assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable).
   { eapply schnorr_owner_framed;[lia|exact FrameF|intros;split;schnorr_distinct Separate|exact FRH]. }
   exists mf;split.
   + eapply exec_schnorr_challenge_body;[exact Tag|exact Copy|exact RCall|exact PCall|exact MCall|exact Final|exact Digest|exact Scalar].
   + split;[exact Limbs|];split;[exact Value|];split.
     * intros b hi Slot;unfold schnorr_challenge_storage in Slot;cbn [In] in Slot.
       destruct Slot as [Slot|[Slot|[Slot|[Slot|[Slot|Slot]]]]];try contradiction;
       inversion Slot;subst;assumption.
     * split.
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact FrameIH|intros b ofs Outside Old;cbn [In] in Outside;intuition].
          ++ eapply lframe_implies;[exact FrameF|intros b ofs Outside Old;cbn [In] in Outside;intuition].
       -- split.
          ++ eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadH|exact ReadF].
          ++ eapply secp_sha_startup_preserved;[exact ReadyH|exact ReadF|exact FrameF|].
             pose proof (proj1 (secp_sha_startup_separate mh be 32 ReadyH ltac:(lia) FEH)) as E.
             pose proof (proj1 (secp_sha_startup_separate mh bb 32 ReadyH ltac:(lia) FBH)) as B.
             intros;split;congruence.
Qed.
