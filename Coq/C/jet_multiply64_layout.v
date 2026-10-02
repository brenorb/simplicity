(** Complete actual multiply_64 against canonical Programs.Arith.multiply.
    All two-local allocation/copy/read/helper/write/free operations follow from
    initial frame contracts, including arbitrary valid cursors and crossings. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_frame_layout C.jet_frame_spec C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_context C.jet_guarantees C.jet_canonical C.jet_constant_layout C.jet_complement_wide_layout.
Require Import C.jet_two_word_input C.jet_umul128_layout C.jet_u128_mul_layout C.jet_write128_layout.
Require Import C.jet_multiply_spec C.jet_multiply64_spec C.jet_multiply64_exec C.jet_frame_u128_initial.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_multiply64_layout_matches_spec env m bd dbase bs sbase bi bw edge outedge
    (x y : Ty.tySem (Word 6)) cursor rc :
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned - 128 ->
  frame_input_word_at m bi edge rc x -> frame_input_word_at m bi edge (rc + 64) y ->
  write_frame_at m bd dbase bw outedge cursor 128 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_multiply_64)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor (encode (@multiply_word_spec 6 Alg.CoreFunSem (x,y))) /\
    write_prefix_at m mf bw outedge cursor /\ frame_fields_at mf bd dbase bw outedge (cursor - 128) /\
    (forall chunk bb ofs, Mem.valid_block m bb ->
      (bb <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (bb <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 128) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs).
Proof.
  intros HB HA Hfields Hrc HX HY Hout.
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
  { eapply frame_input_bits_at_preserved; [|exact HX]. intros ofs w HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (HYc : frame_input_word_at mc bi edge (rc + 64) y).
  { eapply frame_input_bits_at_preserved; [|exact HY]. intros ofs w HL. rewrite HCopyLoad by exact HVi; exact HL. }
  assert (Hbase : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (frame_u128_slots_writable mc bl br Hlocals) as (PC & PRlo & PRhi).
  destruct (eval_read_wide_word_at W64 mc bl 0 bi edge rc x Hbase ltac:(change (0 <= rc <= Int64.max_unsigned - 64); lia)
    HCopyFields HXc PC ltac:(congruence)) as (mr1 & a & HR1 & Hax & HF1 & HM1 & HP1 & HV1).
  assert (HYr : frame_input_word_at mr1 bi edge (rc + 64) y).
  { eapply frame_input_bits_at_preserved; [|exact HYc]. intros ofs w HL. rewrite HM1 by auto; exact HL. }
  assert (PC1 : Mem.valid_access mr1 Mint64 bl 8 Writable).
  { eapply permissions_preserve_access; eauto. }
  destruct (eval_read_wide_word_at W64 mr1 bl 0 bi edge (rc + 64) y Hbase
    ltac:(change (0 <= rc + 64 <= Int64.max_unsigned - 64); lia) HF1 HYr PC1 ltac:(congruence))
    as (mr2 & b & HR2 & Hby & HF2 & HM2 & HP2 & HV2).
  assert (HReadPerm : forall bb ofs kind p, Mem.perm mc bb ofs kind p -> Mem.perm mr2 bb ofs kind p).
  { intros bb ofs kind p H. apply HP2, HP1; exact H. }
  assert (PRlo2 : Mem.valid_access mr2 Mint64 br 0 Writable)
    by (eapply permissions_preserve_access; eauto).
  assert (PRhi2 : Mem.valid_access mr2 Mint64 br 8 Writable)
    by (eapply permissions_preserve_access; eauto).
  destruct (eval_u128_mul_layout mr2 br 0 a b Hbase PRlo2 PRhi2)
    as (mk & HM & Hlo & Hhi & HHnumeric & HLnumeric & HMulLoad & HMulPerm & HMulNext).
  assert (HBeforeLoad : forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk mk bb ofs = Mem.load chunk m bb ofs).
  { intros chunk bb ofs HV. destruct (Hfresh bb HV) as [Nl Nr].
    rewrite HMulLoad by auto. rewrite HM2, HM1 by auto. apply HCopyLoad; exact HV. }
  assert (HBeforePerm : forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mk bb ofs kind p).
  { intros bb ofs kind p H. apply HMulPerm, HP2, HP1, HCopyPerm; exact H. }
  assert (HOutK : write_frame_at mk bd dbase bw outedge cursor 128).
  { eapply write_frame_at_preserved; [|exact HBeforePerm|exact Hout].
    intros chunk bb ofs v [-> | ->] HL; rewrite HBeforeLoad by assumption; exact HL. }
  destruct (eval_write128_layout mk bd dbase bw outedge cursor br 0 (umul128_result_hi a b) (umul128_result_lo a b)
    Hbase ltac:(congruence) ltac:(congruence) Hhi Hlo HOutK)
    as (me & HW & Houtput & Hprefix & HOutFields & HWriteLoad & HWritePerm & HWriteValid).
  assert (HLocalsE : frame_u128_local_permissions me bl br).
  { eapply frame_u128_permissions_preserved; [exact HWritePerm|].
    eapply frame_u128_permissions_preserved; [exact HMulPerm|].
    eapply frame_u128_permissions_preserved; [exact HReadPerm|exact Hlocals]. }
  destruct (free_frame_u128_locals me bl br Hdistinct HLocalsE) as (mf & HF & HAfterLoad & HAfterPerm & HAfterNext).
  rewrite (multiply64_product_representation x y a b Hax Hby) in Houtput.
  exists mf. split.
  - eapply eval_multiply64_composes with (bl := bl) (br := br); eauto; congruence.
  - split.
    + eapply frame_output_cells_preserved; [|exact Houtput]. intros ofs w HL. rewrite HAfterLoad by assumption; exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. rewrite HBeforeLoad by exact HVw; exact HL.
        -- intros ofs w HL. rewrite HAfterLoad by assumption; exact HL.
      * split.
        -- destruct HOutFields as [HE HO]. split; rewrite HAfterLoad by assumption; assumption.
        -- intros chunk bb ofs HV Hbd Hbw. destruct (Hfresh bb HV) as [Nl Nr].
           rewrite HAfterLoad by assumption. rewrite HWriteLoad by assumption. apply HBeforeLoad; exact HV.
Qed.

Theorem multiply64_local_spec : jet_local_spec f_simplicity_multiply_64
  (Ty.Prod (Word 6) (Word 6)) (Word 7) (fun xy => @multiply_word_spec 6 Alg.CoreFunSem xy).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 7))) with 128 in *.
  change (Z.of_nat (bitSize (Ty.Prod (Word 6) (Word 6)))) with 128 in Hmax.
  apply frame_input_word_pair_encode in Hin. destruct Hin as [HX HY].
  change (frame_input_word_at m bi edge (rc + 64) y) in HY.
  eapply eval_multiply64_layout_matches_spec; eauto; lia.
Qed.

Theorem multiply64_context : jet_context_for f_simplicity_multiply_64 (@multiply_word_spec 6).
Proof. exact (jet_context _ _ (multiply_word_spec_parametric 6) multiply64_local_spec ltac:(vm_compute; lia)). Qed.
Definition multiply64_guarantees := jet_local_spec_guarantees _ _ _ _ multiply64_local_spec.
Definition multiply64_context_guarantees :=
  jet_context_guarantees _ _ (multiply_word_spec_parametric 6) multiply64_local_spec ltac:(vm_compute; lia).
