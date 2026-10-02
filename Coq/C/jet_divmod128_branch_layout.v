(** Derive both actual public C branches, their helper/writer calls and canonical
    output from initial branch memory. No intermediate executions are assumed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_wide C.jet_wide_spec C.jet_minmax_wide_layout.
Require Import C.jet_readBit_layout.
Require Import C.jet_frame_layout C.jet_frame_spec C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_write_wide_mixed_sequence.
Require Import C.jet_division_core_spec C.jet_predicate_spec C.jet_divmod96_value.
Require Import C.jet_order_spec.
Require Import C.jet_divmod128_allocate C.jet_divmod128_spec C.jet_divmod128_expr.
Require Import C.jet_divmod128_helpers C.jet_divmod128_entry C.jet_divmod128_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod128_wide_decode s w : Int64.unsigned w < word_modulus (wide_log s) ->
  decode_wide s (Int64.zero_ext (wide_bits s) w) =
    @fromZ (WordToZ (wide_log s)) (Int64.unsigned w).
Proof.
  intros Hrange. apply wide_input_value_decode. rewrite to_fromZ.
  change (Int64.unsigned w = Int64.unsigned w mod word_modulus (wide_log s)).
  symmetry. apply Z.mod_small. pose proof (Int64.unsigned_range w); lia.
Qed.

Theorem exec_divmod128_branch_layout le m bl bqh bql br bd dbase bw outedge cursor
    (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5)) (y : Ty.tySem (Word 6)) ah am al b :
  le!_ah = Some (Vlong ah) -> le!_am = Some (Vlong am) -> le!_al = Some (Vlong al) ->
  le!_b = Some (Vlong b) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'5 = Some (Vint (bit_int (divmod128_guard ah b))) ->
  Int64.unsigned ah = @toZ (WordToZ 6) xh -> Int64.unsigned am = @toZ (WordToZ 5) xm ->
  Int64.unsigned al = @toZ (WordToZ 5) xl -> Int64.unsigned b = @toZ (WordToZ 6) y ->
  divmod128_local_distinct bl bqh bql br -> divmod128_local_permissions m bl bqh bql br ->
  (forall bb, bb = bd \/ bb = bw -> bb <> bqh /\ bb <> bql /\ bb <> br) ->
  write_frame_at m bd dbase bw outedge cursor 128 ->
  exists me lef,
    Clight2.exec_stmt ge0 (divmod128_env bl bqh bql br) le m divmod128_branch_stmt E0 lef me Out_normal /\
    frame_output_cells_at me bw outedge cursor
      (encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))) /\
    write_prefix_at m me bw outedge cursor /\
    frame_fields_at me bd dbase bw outedge (cursor - 128) /\
    (forall chunk bb ofs, bb <> bqh -> bb <> bql -> bb <> br ->
      (bb <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (bb <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 128) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk me bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm me bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block me bb).
Proof.
  intros HA HAM HAL HB HD HG Hah Ham Hal Hb Hdistinct Hlocals Hsep Hout.
  pose proof (divmod128_conditions_match xh xm xl y ah am al b Hah Ham Hal Hb) as Hcond.
  destruct Hdistinct as (Hlh & Hll & Hlr & Hhl & Hhr & Hlrq).
  destruct (divmod128_local_slots_writable m bl bqh bql br Hlocals) as (HPL & HPH & HPQ & HPR).
  destruct (Hsep bd ltac:(auto)) as (NDqh & NDql & NDr).
  destruct (Hsep bw ltac:(auto)) as (NWqh & NWql & NWr).
  destruct (divmod128_guard ah b) eqn:Hguard.
  - destruct (proj1 (divmod128_guard_preconditions ah b) Hguard) as [Hnorm Hbound].
    pose proof (word_value_bounds 5 xm) as Hxm. pose proof (word_value_bounds 5 xl) as Hxl.
    assert (HamB : Int64.unsigned am < divmod96_radix) by (rewrite Ham; exact (proj2 Hxm)).
    assert (HalB : Int64.unsigned al < divmod96_radix) by (rewrite Hal; exact (proj2 Hxl)).
    destruct (eval_divmod128_helpers m bqh Ptrofs.zero bql Ptrofs.zero br Ptrofs.zero ah am al b
      Hnorm Hbound HamB HalB HPH HPQ HPR ltac:(left; exact Hhl) ltac:(left; exact Hhr) ltac:(left; exact Hlrq))
      as (mh & mk & qh & ql & r1 & rf & HC1 & HR1 & HC2 & HQH & HQL & HRF &
        Hqh & Hql & Hrf & Hbalance & HmemH & HpermH & HnextH).
    assert (HBeforeLoad : forall chunk bb ofs v, bb = bd \/ bb = bw ->
        Mem.load chunk m bb ofs = Some v -> Mem.load chunk mk bb ofs = Some v).
    { intros chunk bb ofs v Hbb HL. destruct (Hsep bb Hbb) as (HqhN & HqlN & HrN).
      rewrite HmemH by auto. exact HL. }
    assert (HOutK : write_frame_at mk bd dbase bw outedge cursor 128).
    { eapply write_frame_at_preserved; eauto. }
    destruct (write_wide_mixed_run_layout mk bd dbase bw outedge cursor [(W32,qh);(W32,ql);(W64,rf)] HOutK)
      as (me & Hrun & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    cbn [write_wide_mixed_run] in Hrun.
    destruct Hrun as (mw1 & HW1 & HM1 & mw2 & HW2 & HM2 & last & HW3 & HM3 & Hdone). subst last.
    assert (HQLw : Mem.load Mint64 mw1 bql 0 = Some (Vlong ql)).
    { rewrite HM1; [exact HQL|congruence|congruence]. }
    assert (HRFw : Mem.load Mint64 mw2 br 0 = Some (Vlong rf)).
    { rewrite HM2, HM1; [exact HRF|congruence|congruence|congruence|congruence]. }
    assert (HcanNorm : word_modulus 6 <= 2 * @toZ (WordToZ 6) y) by (rewrite <- Hb; exact Hnorm).
    assert (HcanBound : @toZ (WordToZ 7) (xh,(xm,xl)) < @toZ (WordToZ 6) y * word_modulus 6).
    { apply Z.ltb_lt. rewrite <- division_high_less, lt_word_spec_numeric.
      cbn [fst]. apply Z.ltb_lt. rewrite <- Hah, <- Hb. exact Hbound. }
    assert (Hrepr : ((@fromZ (WordToZ 5) (Int64.unsigned qh), @fromZ (WordToZ 5) (Int64.unsigned ql)),
        @fromZ (WordToZ 6) (Int64.unsigned rf)) = @div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y)).
    { apply divmod128_valid_representation; try assumption.
      - rewrite <- Hb; exact Hrf.
      - rewrite (divmod128_input_value xh xm xl ah am al Hah Ham Hal), <- Hb. exact Hbalance. }
    assert (Hcells : wide_mixed_cells [(W32,qh);(W32,ql);(W64,rf)] =
        encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))).
    { change (encode (decode_wide W32 (Int64.zero_ext 32 qh)) ++
        (encode (decode_wide W32 (Int64.zero_ext 32 ql)) ++
          (encode (decode_wide W64 (Int64.zero_ext 64 rf)) ++ [])) =
        encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))).
      rewrite !app_nil_r, !divmod128_wide_decode by (first [exact (proj2 Hqh)|exact (proj2 Hql)|apply Int64.unsigned_range]).
      rewrite <- Hrepr. apply app_assoc. }
    exists me, (divmod128_valid_env le r1 qh ql rf). split.
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
      * apply eval_Etempvar; exact HG.
      * reflexivity.
      * eapply exec_divmod128_valid_composes; eauto.
    + split; [rewrite <- Hcells; exact Houtput|]. split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. apply HBeforeLoad; [right; reflexivity|exact HL].
        -- intros ofs w HL. exact HL.
      * split; [exact Hfields|]. split.
        -- intros chunk bb ofs Hh Hl Hr Hbd Hbw. rewrite Hmemory by assumption. rewrite HmemH by auto. reflexivity.
        -- split.
           ++ intros bb ofs kind p HP. apply Hperm, HpermH; exact HP.
           ++ intros bb HV. apply Hvalid. unfold Mem.valid_block in *. rewrite HnextH. exact HV.
  - set (ones := Int64.repr Int64.max_unsigned).
    destruct (write_wide_mixed_run_layout m bd dbase bw outedge cursor [(W64,ones);(W64,ones)] Hout)
      as (me & Hrun & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
    cbn [write_wide_mixed_run] in Hrun.
    destruct Hrun as (mw & HW1 & HM1 & last & HW2 & HM2 & Hdone). subst last.
    assert (HU : Int64.unsigned ones = Int64.max_unsigned).
    { unfold ones. apply Int64.unsigned_repr. split; [change (0 <= 18446744073709551615); lia|lia]. }
    assert (Hcells : wide_mixed_cells [(W64,ones);(W64,ones)] =
        encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))).
    { change (encode (decode_wide W64 (Int64.zero_ext 64 ones)) ++
        (encode (decode_wide W64 (Int64.zero_ext 64 ones)) ++ []) =
        encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))).
      rewrite app_nil_r, divmod128_wide_decode by apply Int64.unsigned_range.
      rewrite HU.
      change (@encode (Word 7) ((@fromZ (WordToZ 6) Int64.max_unsigned,
        @fromZ (WordToZ 6) Int64.max_unsigned)) =
        encode (@div2n1n_word_spec 6 Alg.CoreFunSem ((xh,(xm,xl)),y))).
      apply f_equal. exact (divmod128_invalid_representation (xh,(xm,xl)) y Hcond). }
    exists me, le. split.
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
      * apply eval_Etempvar; exact HG.
      * reflexivity.
      * eapply exec_divmod128_invalid_composes; try eassumption; reflexivity.
    + split; [rewrite <- Hcells; exact Houtput|]. split; [exact Hprefix|]. split; [exact Hfields|].
      split; [intros; apply Hmemory; assumption|]. tauto.
Qed.
