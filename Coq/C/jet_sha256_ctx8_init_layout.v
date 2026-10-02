(** Complete actual sha_256_ctx_8_init against literal ctx8Init. The initial
    frame contract derives all five local allocations, both copies, all
    initializer stores, writer calls and cleanup, at arbitrary valid cursors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_guarantees C.jet_canonical C.jet_constant_layout.
Require Import C.jet_four_locals C.jet_sha256_ctx8_init_spec C.jet_sha256_ctx8_init_exec C.jet_sha256_ctx8_init_prepare.
Require Import C.jet_write_sha256_context_empty_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma ctx_init_blocks bl bi bc br : blocks_of_env ge0 (ctx_init_env bl bi bc br) =
  [(bc,0,88);(bl,0,16);(bi,0,32);(br,0,88)].
Proof. reflexivity. Qed.

Theorem eval_sha256_ctx8_init_layout_matches_spec env m bf base bs sbase source bw edge outedge cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase source edge rc ->
  write_frame_at m bf base bw outedge cursor 830 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_sha_256_ctx_8_init)
      [Vptr bf (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@sha256_ctx8_init_spec Alg.CoreFunSem tt)) /\
    write_prefix_at m mf bw outedge cursor /\ frame_fields_at mf bf base bw outedge (cursor - 830) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 830) / 64) \/ write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HB HA HSource Hout.
  pose proof HSource as [HSE HSO]. pose proof Hout as [_ [[HDE HDO] _]].
  assert (VS : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (VD : Mem.valid_block m bf) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bf base bw outedge cursor 830 ltac:(lia) Hout)
    as (_ & _ & _ & initial & HInitial).
  assert (VW : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitial).
  destruct (prepare_sha256_ctx8_init m bs sbase source edge rc HSource)
    as (ma & mb & mc & md & ms & mi & mx & bl & bi & bc & br & srcbytes & ctxbytes &
      AS & AI & AC & AR & HSrc & HSrcCopy & HInit & HCtx & HCtxCopy & Hsep & Hlocals & Hfresh &
      HOutX & HCounterX & HOverflowX & HArrayX & HBeforeLoad & HBeforePerm).
  destruct Hsep as (Nsi & Nsc & Nsr & Nic & Nir & Ncr).
  destruct (Hfresh bs VS) as (NSs & NSi & NSc & NSr).
  destruct (Hfresh bf VD) as (NDs & NDi & NDc & NDr).
  destruct (Hfresh bw VW) as (NWs & NWi & NWc & NWr).
  assert (HOutPrepared : write_frame_at mx bf base bw outedge cursor 830).
  { eapply write_frame_at_preserved; [|exact HBeforePerm|exact Hout].
    intros chunk b ofs v [-> | ->] HL; rewrite HBeforeLoad by assumption; exact HL. }
  destruct (eval_write_sha256_context_empty_layout mx bf base bw outedge cursor bc 0 bi 0
    ltac:(lia) ltac:(change (88 <= 18446744073709551615); lia)
    ltac:(lia) ltac:(change (32 <= 18446744073709551615); lia)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    HCounterX HOutX HOverflowX HArrayX HOutPrepared)
    as (me & HWrite & HCells & HPrefix & HFields & HMemory & HWritePerm & HWriteValid).
  assert (HFreeSep : four_local_distinct bc bl bi br) by (repeat split; congruence).
  destruct Hlocals as (PS & PI & PC & PR).
  assert (HFreePerm : four_local_permissions me bc 88 bl 16 bi 32 br 88).
  { repeat split; intros ofs H.
    all: apply HWritePerm; first [apply PC|apply PS|apply PI|apply PR]; exact H. }
  destruct (free_four_locals me bc 88 bl 16 bi 32 br 88 HFreeSep HFreePerm)
    as (mf & HFree & HAfterLoad & HAfterPerm & HAfterNext).
  exists mf. split.
  - eapply eval_sha256_ctx8_init_composes with (bl := bl) (bi := bi) (bc := bc) (br := br); eauto; try congruence.
  - split.
    + eapply frame_output_cells_preserved; [|exact HCells]. intros ofs w HL; rewrite HAfterLoad by assumption; exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact HPrefix].
        -- intros ofs w HL; rewrite HBeforeLoad by exact VW; exact HL.
        -- intros ofs w HL; rewrite HAfterLoad by assumption; exact HL.
      * split.
        -- destruct HFields as [HE HO]. split; rewrite HAfterLoad by assumption; assumption.
        -- intros chunk b ofs HV Hbf Hbw. destruct (Hfresh b HV) as (Ns & Ni & Nc & Nr).
           rewrite HAfterLoad by assumption. rewrite HMemory by assumption. apply HBeforeLoad; exact HV.
Qed.

Theorem sha256_ctx8_init_local_spec : jet_local_spec f_simplicity_sha_256_ctx_8_init Ty.Unit sha256_ctx8_type
  (fun a => @sha256_ctx8_init_spec Alg.CoreFunSem a).
Proof.
  intros env m bf base bs sbase source bw edge outedge cursor rc [] HB HA HF _ _ _ Hout.
  rewrite sha256_ctx8_type_bits in Hout |- *. eapply eval_sha256_ctx8_init_layout_matches_spec; eauto.
Qed.
Theorem sha256_ctx8_init_context : jet_context_for f_simplicity_sha_256_ctx_8_init (@sha256_ctx8_init_spec).
Proof. exact (jet_context _ _ sha256_ctx8_init_spec_parametric sha256_ctx8_init_local_spec ltac:(vm_compute; lia)). Qed.
Definition sha256_ctx8_init_guarantees := jet_local_spec_guarantees _ _ _ _ sha256_ctx8_init_local_spec.
Definition sha256_ctx8_init_context_guarantees :=
  jet_context_guarantees _ _ sha256_ctx8_init_spec_parametric sha256_ctx8_init_local_spec ltac:(vm_compute; lia).
