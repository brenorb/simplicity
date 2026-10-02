(** Derive the four actual allocations, by-value frame copy and four readers
    from the original input frame. Intermediate calls are conclusions only. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_wide C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_complement_wide_layout C.jet_divmod128_allocate C.jet_divmod128_readers.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod128_local_permissions_preserved m mf bl bqh bql br :
  (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) ->
  divmod128_local_permissions m bl bqh bql br -> divmod128_local_permissions mf bl bqh bql br.
Proof.
  intros Hperm (PL & PH & PQ & PR). repeat split; intros ofs Hrange;
    apply Hperm; first [apply PL|apply PH|apply PQ|apply PR]; exact Hrange.
Qed.

Theorem eval_divmod128_initial m bs sbase bi edge rc
    (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5)) (y : Ty.tySem (Word 6)) :
  frame_fields_at m bs sbase bi edge rc -> 0 <= rc <= Int64.max_unsigned - 192 ->
  frame_input_word_at m bi edge rc xh -> frame_input_word_at m bi edge (rc + 64) xm ->
  frame_input_word_at m bi edge (rc + 96) xl -> frame_input_word_at m bi edge (rc + 128) y ->
  exists ma mb mc md mcopy mr1 mr2 mr3 mr4 bl bqh bql br bytes ah am al b,
    Mem.alloc m 0 16 = (ma,bl) /\ Mem.alloc ma 0 8 = (mb,bqh) /\
    Mem.alloc mb 0 8 = (mc,bql) /\ Mem.alloc mc 0 8 = (md,br) /\
    Mem.loadbytes md bs sbase 16 = Some bytes /\ Mem.storebytes md bl 0 bytes = Some mcopy /\
    Clight2.eval_funcall ge0 mcopy (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr1 (Vlong ah) /\
    Clight2.eval_funcall ge0 mr1 (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong am) /\
    Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong al) /\
    Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr4 (Vlong b) /\
    Int64.unsigned ah = @toZ (WordToZ 6) xh /\ Int64.unsigned am = @toZ (WordToZ 5) xm /\
    Int64.unsigned al = @toZ (WordToZ 5) xl /\ Int64.unsigned b = @toZ (WordToZ 6) y /\
    divmod128_local_distinct bl bqh bql br /\ divmod128_local_permissions mr4 bl bqh bql br /\
    (forall bb, Mem.valid_block m bb -> bb <> bl /\ bb <> bqh /\ bb <> bql /\ bb <> br) /\
    (forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk mr4 bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mr4 bb ofs kind p).
Proof.
  intros [HSE HSO] Hrc Hxh Hxm Hxl Hy.
  assert (Hbs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (Hbi : Mem.valid_block m bi).
  { destruct (wide_input_first_load W64 m bi edge rc xh Hxh) as [w HL].
    eapply load_valid_block; exact HL. }
  destruct (allocate_divmod128_locals m)
    as (ma & mb & mc & md & bl & bqh & bql & br & HA & HB & HC & HD & Hdistinct & Hlocals & Hfresh & Hload & Hperm).
  destruct (Hfresh bs Hbs) as (NS & _). destruct (Hfresh bi Hbi) as (NI & _).
  assert (HSEd : Mem.load Mptr md bs sbase = Some (Vptr bi (Ptrofs.repr edge))).
  { rewrite Hload by exact Hbs. exact HSE. }
  assert (HSOd : Mem.load Mint64 md bs (sbase + 8) = Some (Vlong (Int64.repr rc))).
  { rewrite Hload by exact Hbs. exact HSO. }
  destruct (frame_loadbytes_at md bs sbase _ _ HSEd HSOd) as [bytes Hbytes].
  pose proof (Mem.loadbytes_length _ _ _ _ _ Hbytes) as Hlen.
  assert (PC : Mem.range_perm md bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm md bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply (proj1 Hlocals); exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes md bl 0 bytes PC) as [mcopy Hcopy].
  destruct (frame_copy_fields_at md mcopy bs sbase bl bytes _ _ Hbytes Hcopy HSEd HSOd) as [HLE HLO].
  assert (HCopyLoad : forall ofs w, Mem.load Mint64 m bi ofs = Some (Vlong w) ->
      Mem.load Mint64 mcopy bi ofs = Some (Vlong w)).
  { intros ofs w HL. erewrite Mem.load_storebytes_other; [rewrite Hload by exact Hbi; exact HL|exact Hcopy|auto]. }
  assert (Hxc : frame_input_word_at mcopy bi edge rc xh)
    by (eapply frame_input_bits_at_preserved; eauto).
  assert (Hmc : frame_input_word_at mcopy bi edge (rc + 64) xm)
    by (eapply frame_input_bits_at_preserved; eauto).
  assert (Hlc : frame_input_word_at mcopy bi edge (rc + 96) xl)
    by (eapply frame_input_bits_at_preserved; eauto).
  assert (Hyc : frame_input_word_at mcopy bi edge (rc + 128) y)
    by (eapply frame_input_bits_at_preserved; eauto).
  assert (HCopyPerm : forall bb ofs kind p, Mem.perm md bb ofs kind p -> Mem.perm mcopy bb ofs kind p).
  { intros bb ofs kind p HP. eapply Mem.perm_storebytes_1; eauto. }
  assert (HCopyLocals : divmod128_local_permissions mcopy bl bqh bql br).
  { eapply divmod128_local_permissions_preserved; eauto. }
  destruct (divmod128_local_slots_writable mcopy bl bqh bql br HCopyLocals) as (Pcursor & _).
  assert (Hbase : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (eval_divmod128_readers mcopy bl 0 bi edge rc xh xm xl y Hbase Hrc
    (conj HLE HLO) Hxc Hmc Hlc Hyc Pcursor ltac:(congruence))
    as (mr1 & mr2 & mr3 & mr4 & ah & am & al & b & HR1 & HR2 & HR3 & HR4 &
      Hah & Ham & Hal & Hb & Hfields & HReadLoad & HReadPerm & HReadValid).
  exists ma, mb, mc, md, mcopy, mr1, mr2, mr3, mr4, bl, bqh, bql, br, bytes, ah, am, al, b.
  do 15 (split; [assumption|]). split.
  - eapply divmod128_local_permissions_preserved; eauto.
  - split; [exact Hfresh|]. split.
    + intros chunk bb ofs HV. destruct (Hfresh bb HV) as (Nbl & _).
      rewrite HReadLoad by auto. erewrite Mem.load_storebytes_other; [apply Hload; exact HV|exact Hcopy|auto].
    + intros bb ofs kind p HP. apply HReadPerm, HCopyPerm, Hperm; exact HP.
Qed.
