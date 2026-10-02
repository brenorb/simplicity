(** Complete public DivMod128_64 execution against its literal Simplicity
    program. Every allocation/copy/reader/helper/writer/free is derived from
    original frames, with arbitrary valid cursors and initial output bits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_spec C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_slice C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_guarantees C.jet_canonical C.jet_readBit_layout.
Require Import C.jet_constant_layout.
Require Import C.jet_arith8_layout_exec C.jet_division_core_spec.
Require Import C.jet_divmod128_spec C.jet_divmod128_allocate C.jet_divmod128_entry.
Require Import C.jet_divmod128_exec C.jet_divmod128_initial C.jet_divmod128_branch_layout C.jet_divmod128_free.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_divmod128_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5)) (y : Ty.tySem (Word 6)) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 192 ->
  frame_input_word_at m bi edge rc xh -> frame_input_word_at m bi edge (rc + 64) xm ->
  frame_input_word_at m bi edge (rc + 96) xl -> frame_input_word_at m bi edge (rc + 128) y ->
  write_frame_at m bd dbase bw outedge cursor 128 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_div_mod_128_64)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 128) /\
    (forall chunk bb ofs, Mem.valid_block m bb ->
      (bb <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (bb <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 128) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs).
Proof.
  intros HSbase HSAlign Hfields Hrc Hxh Hxm Hxl Hy Hout.
  pose proof Hout as [_ [[HDE HDO] _]].
  assert (HVd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 128 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (HVw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (HVs : Mem.valid_block m bs).
  { destruct Hfields as [HE HO]. eapply load_valid_block; exact HE. }
  destruct (eval_divmod128_initial m bs sbase bi edge rc xh xm xl y Hfields Hrc Hxh Hxm Hxl Hy)
    as (ma & mb & mc & md & mcopy & mr1 & mr2 & mr3 & mr4 & bl & bqh & bql & br & bytes & ah & am & al & b &
      HA & HB & HC & HD & Hbytes & Hcopy & HR1 & HR2 & HR3 & HR4 & Hah & Ham & Hal & Hb &
      Hdistinct & Hlocals & Hfresh & HBeforeLoad & HBeforePerm).
  destruct (Hfresh bd HVd) as (NDl & NDqh & NDql & NDr).
  destruct (Hfresh bw HVw) as (NWl & NWqh & NWql & NWr).
  destruct (Hfresh bs HVs) as (NSl & _).
  assert (HOutR : write_frame_at mr4 bd dbase bw outedge cursor 128).
  { eapply write_frame_at_preserved; [|exact HBeforePerm|exact Hout].
    intros chunk bb ofs v [-> | ->] HL; rewrite HBeforeLoad by assumption; exact HL. }
  set (leR := PTree.set _t'5 (Vint (bit_int (divmod128_guard ah b)))
    (divmod128_read_env (divmod128_temps env bd dbase bs sbase) ah am al b)).
  assert (Hsep : forall bb, bb = bd \/ bb = bw -> bb <> bqh /\ bb <> bql /\ bb <> br).
  { intros bb [-> | ->]; auto. }
  destruct (exec_divmod128_branch_layout leR mr4 bl bqh bql br bd dbase bw outedge cursor xh xm xl y ah am al b
    ltac:(unfold leR, divmod128_read_env, divmod128_read_set; divmod128_lookup)
    ltac:(unfold leR, divmod128_read_env, divmod128_read_set; divmod128_lookup)
    ltac:(unfold leR, divmod128_read_env, divmod128_read_set; divmod128_lookup)
    ltac:(unfold leR, divmod128_read_env, divmod128_read_set; divmod128_lookup)
    ltac:(unfold leR, divmod128_read_env, divmod128_read_set, divmod128_temps, le_arith8_layout; divmod128_lookup)
    ltac:(unfold leR; apply PTree.gss) Hah Ham Hal Hb Hdistinct Hlocals Hsep HOutR)
    as (me & lef & Hbranch & Houtput & Hprefix & HOutFields & Hmemory & Hperm & Hvalid).
  assert (HLocalsE : divmod128_local_permissions me bl bqh bql br).
  { eapply divmod128_local_permissions_preserved; eauto. }
  destruct Hdistinct as (Nlh & Nll & Nlr & Nhq & Nhr & Nqr).
  destruct HLocalsE as (PL & PH & PQ & PR).
  destruct (free_divmod128_locals me bl bqh bql br Nlh Nll Nlr Nhq Nhr Nqr PL PH PQ PR)
    as (mf & Hfree & HAfterLoad & HAfterPerm & Hnext).
  exists mf. split.
  - eapply eval_divmod128_composes; eauto; congruence.
  - split.
    + eapply frame_output_cells_preserved; [|exact Houtput].
      intros ofs w HL. rewrite HAfterLoad by assumption. exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. rewrite HBeforeLoad by exact HVw. exact HL.
        -- intros ofs w HL. rewrite HAfterLoad by assumption. exact HL.
      * split.
        -- destruct HOutFields as [HE HO]. split; rewrite HAfterLoad by assumption; assumption.
        -- intros chunk bb ofs HV Hbd Hbw. destruct (Hfresh bb HV) as (Nl & Nh & Nq & Nr).
           rewrite HAfterLoad by assumption. rewrite Hmemory by assumption. apply HBeforeLoad; exact HV.
Qed.

Theorem divmod128_local_spec : jet_local_spec f_simplicity_div_mod_128_64
  (Ty.Prod (Word 7) (Word 6)) (Word 7)
  (fun xy => @div2n1n_word_spec 6 Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [[xh [xm xl]] y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 7))) with 128 in *.
  change (Z.of_nat (bitSize (Ty.Prod (Word 7) (Word 6)))) with 192 in Hmax.
  change (frame_input_cells_at m bi edge rc
    ((encode xh ++ (encode xm ++ encode xl)) ++ encode y)) in Hin.
  rewrite !frame_input_cells_at_app, !encode_word_length in Hin.
  destruct Hin as [[HX [HM HL]] HY].
  apply frame_input_word_at_encode in HX. apply frame_input_word_at_encode in HM.
  apply frame_input_word_at_encode in HL. apply frame_input_word_at_encode in HY.
  replace (rc + Z.of_nat (2 ^ 6) + Z.of_nat (2 ^ 5)) with (rc + 96) in HL by (cbn; lia).
  replace (rc + Z.of_nat (length (encode xh ++ (encode xm ++ encode xl)))) with (rc + 128) in HY
    by (rewrite !app_length, !encode_word_length; cbn; lia).
  eapply eval_divmod128_layout_matches_spec; eauto; cbn in *; lia.
Qed.

Theorem divmod128_context : jet_context_for f_simplicity_div_mod_128_64 (@div2n1n_word_spec 6).
Proof.
  exact (jet_context _ _ (div2n1n_word_spec_parametric 6) divmod128_local_spec ltac:(vm_compute; lia)).
Qed.
Definition divmod128_guarantees := jet_local_spec_guarantees _ _ _ _ divmod128_local_spec.
Definition divmod128_context_guarantees :=
  jet_context_guarantees _ _ (div2n1n_word_spec_parametric 6) divmod128_local_spec ltac:(vm_compute; lia).
