(** Complete actual full_multiply_64 against canonical Programs.Arith.full_multiply.
    Every allocation/copy/read/helper/write/free is derived from initial frames;
    valid cursors, crossings and unrelated output bits remain unrestricted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_frame_layout C.jet_frame_spec C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_guarantees C.jet_canonical C.jet_constant_layout C.jet_complement_wide_layout.
Require Import C.jet_umul128_layout C.jet_u128_mul_layout C.jet_u128_accum_value C.jet_u128_accum_layout.
Require Import C.jet_write128_layout C.jet_frame_u128_initial C.jet_read_wide_quad_layout.
Require Import C.jet_full_multiply_word C.jet_full_multiply64_spec C.jet_full_multiply64_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_full_multiply64_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (x y z w : Ty.tySem (Word 6)) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 256 ->
  frame_input_word_at m bi edge rc x -> frame_input_word_at m bi edge (rc + 64) y ->
  frame_input_word_at m bi edge (rc + 128) z -> frame_input_word_at m bi edge (rc + 192) w ->
  write_frame_at m bd dbase bw outedge cursor 128 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_full_multiply_64)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@fullMultiplier 6 Alg.CoreFunSem ((x,y),(z,w)))) /\
    write_prefix_at m mf bw outedge cursor /\ frame_fields_at mf bd dbase bw outedge (cursor - 128) /\
    (forall chunk bb ofs, Mem.valid_block m bb ->
      (bb <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (bb <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 128) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs).
Proof.
  intros HB HA Hfields Hrc HX HY HZ HW Hout.
  pose proof Hfields as [HSE HSO]. pose proof Hout as [_ [[HDE HDO] _]].
  assert (HVs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (HVd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (wide_input_first_load W64 m bi edge rc x HX) as [firstword HFirst].
  assert (HVi : Mem.valid_block m bi) by (eapply load_valid_block; exact HFirst).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 128 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitial]]]].
  assert (HVw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitial).
  destruct (initialize_frame_u128_input m bs sbase bi edge rc Hfields)
    as (ma & mb & mc & bl & br & bytes & HAllocL & HAllocR & Hbytes & Hcopy & Hdistinct &
      HCopyFields & Hlocals & Hfresh & HCopyLoad & HCopyPerm).
  destruct (Hfresh bs HVs) as [NSl NSr]. destruct (Hfresh bi HVi) as [NIl NIr].
  destruct (Hfresh bd HVd) as [NDl NDr]. destruct (Hfresh bw HVw) as [NWl NWr].
  assert (HXc : frame_input_word_at mc bi edge rc x).
  { eapply frame_input_bits_at_preserved; [|exact HX]. intros ofs v HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (HYc : frame_input_word_at mc bi edge (rc + 64) y).
  { eapply frame_input_bits_at_preserved; [|exact HY]. intros ofs v HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (HZc : frame_input_word_at mc bi edge (rc + 128) z).
  { eapply frame_input_bits_at_preserved; [|exact HZ]. intros ofs v HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (HWc : frame_input_word_at mc bi edge (rc + 192) w).
  { eapply frame_input_bits_at_preserved; [|exact HW]. intros ofs v HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (Hbase : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (frame_u128_slots_writable mc bl br Hlocals) as (PC & PRlo & PRhi).
  destruct (eval_read_wide_quad_at W64 mc bl 0 bi edge rc x y z w Hbase Hrc HCopyFields
    HXc HYc HZc HWc PC ltac:(congruence))
    as (mr1 & mr2 & mr3 & mr4 & a & b & u & v & HR1 & HR2 & HR3 & HR4 & Hax & Hby & Huz & Hvw &
      HReadFields & HReadLoad & HReadPerm & HReadValid).
  assert (HLocalsR : frame_u128_local_permissions mr4 bl br)
    by (eapply frame_u128_permissions_preserved; eauto).
  destruct (frame_u128_slots_writable mr4 bl br HLocalsR) as (_ & PRlo4 & PRhi4).
  destruct (eval_u128_mul_layout mr4 br 0 a b Hbase PRlo4 PRhi4)
    as (mk & HM & Hlo & Hhi & HHnumeric & HLnumeric & HMulLoad & HMulPerm & HMulNext).
  assert (HLocalsK : frame_u128_local_permissions mk bl br)
    by (eapply frame_u128_permissions_preserved; eauto).
  destruct (frame_u128_slots_writable mk bl br HLocalsK) as (_ & PRloK & PRhiK).
  destruct (eval_u128_accum_layout mk br 0 (umul128_result_hi a b) (umul128_result_lo a b) u
    Hbase PRloK PRhiK Hlo Hhi) as (mz & HZcall & HloZ & HhiZ & HZload & HZperm & HZnext).
  assert (HLocalsZ : frame_u128_local_permissions mz bl br)
    by (eapply frame_u128_permissions_preserved; eauto).
  destruct (frame_u128_slots_writable mz bl br HLocalsZ) as (_ & PRloZ & PRhiZ).
  destruct (eval_u128_accum_layout mz br 0
    (u128_accum_hi (umul128_result_hi a b) (umul128_result_lo a b) u)
    (u128_accum_lo (umul128_result_lo a b) u) v Hbase PRloZ PRhiZ HloZ HhiZ)
    as (mw & HWcall & HloW & HhiW & HWload & HWperm & HWnext).
  assert (HBeforeLoad : forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk mw bb ofs = Mem.load chunk m bb ofs).
  { intros chunk bb ofs HV. destruct (Hfresh bb HV) as [Nl Nr].
    rewrite HWload, HZload, HMulLoad by auto. rewrite HReadLoad by auto. apply HCopyLoad; exact HV. }
  assert (HBeforePerm : forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mw bb ofs kind p).
  { intros bb ofs kind p H. apply HWperm, HZperm, HMulPerm, HReadPerm, HCopyPerm; exact H. }
  assert (HOutW : write_frame_at mw bd dbase bw outedge cursor 128).
  { eapply write_frame_at_preserved; [|exact HBeforePerm|exact Hout].
    intros chunk bb ofs v0 [-> | ->] HL; rewrite HBeforeLoad by assumption; exact HL. }
  destruct (eval_write128_layout mw bd dbase bw outedge cursor br 0 (full_multiply64_hi a b u v) (full_multiply64_lo a b u v)
    Hbase ltac:(congruence) ltac:(congruence) HhiW HloW HOutW)
    as (me & Hwrite & Houtput & Hprefix & HOutFields & HWriteLoad & HWritePerm & HWriteValid).
  assert (HLocalsE : frame_u128_local_permissions me bl br).
  { eapply frame_u128_permissions_preserved; [exact HWritePerm|].
    eapply frame_u128_permissions_preserved; [exact HWperm|exact HLocalsZ]. }
  destruct (free_frame_u128_locals me bl br Hdistinct HLocalsE) as (mf & HF & HAfterLoad & HAfterPerm & HAfterNext).
  rewrite (full_multiply64_representation x y z w a b u v Hax Hby Huz Hvw) in Houtput.
  exists mf. split.
  - eapply eval_full_multiply64_composes with (bl := bl) (br := br); eauto; congruence.
  - split.
    + eapply frame_output_cells_preserved; [|exact Houtput]. intros ofs v0 HL. rewrite HAfterLoad by assumption; exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs v0 HL. rewrite HBeforeLoad by exact HVw; exact HL.
        -- intros ofs v0 HL. rewrite HAfterLoad by assumption; exact HL.
      * split.
        -- destruct HOutFields as [HE HO]. split; rewrite HAfterLoad by assumption; assumption.
        -- intros chunk bb ofs HV Hbd Hbw. destruct (Hfresh bb HV) as [Nl Nr].
           rewrite HAfterLoad by assumption. rewrite HWriteLoad by assumption. apply HBeforeLoad; exact HV.
Qed.

Theorem full_multiply64_local_spec : jet_local_spec f_simplicity_full_multiply_64
  (Ty.Prod (Ty.Prod (Word 6) (Word 6)) (Ty.Prod (Word 6) (Word 6))) (Word 7)
  (fun input => @fullMultiplier 6 Alg.CoreFunSem input).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [[x y] [z w]] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 7))) with 128 in *.
  change (Z.of_nat (bitSize (Ty.Prod (Ty.Prod (Word 6) (Word 6)) (Ty.Prod (Word 6) (Word 6))))) with 256 in Hmax.
  apply frame_input_word_quad_encode in Hin. destruct Hin as [HX [HY [HZ HW]]].
  change (frame_input_word_at m bi edge (rc + 64) y) in HY.
  change (frame_input_word_at m bi edge (rc + 128) z) in HZ.
  change (frame_input_word_at m bi edge (rc + 192) w) in HW.
  eapply eval_full_multiply64_layout_matches_spec; eauto; lia.
Qed.

Lemma full_multiply64_spec_parametric : Alg.Core.Parametric (@fullMultiplier 6).
Proof. intros alg1 alg2 R. apply fullMultiplier_Parametric. Qed.
Theorem full_multiply64_context : jet_context_for f_simplicity_full_multiply_64 (@fullMultiplier 6).
Proof. exact (jet_context _ _ full_multiply64_spec_parametric full_multiply64_local_spec ltac:(vm_compute; lia)). Qed.
Definition full_multiply64_guarantees := jet_local_spec_guarantees _ _ _ _ full_multiply64_local_spec.
Definition full_multiply64_context_guarantees :=
  jet_context_guarantees _ _ full_multiply64_spec_parametric full_multiply64_local_spec ltac:(vm_compute; lia).
