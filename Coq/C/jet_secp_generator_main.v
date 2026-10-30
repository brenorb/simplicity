(** Original Strauss generator branch through the final point correction.
    Scalar splitting, both wNAF calls and the complete point stage execute
    here. The two original memset steps remain explicit deferred premises.
    Entry/preparation and final Strauss-local frees are separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_rescale_literal
  C.jet_secp_canonical_zero C.jet_secp_canonical_scalar C.jet_secp_point_set_bit
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_scalar_split128_literal C.jet_secp_statement_prefix C.jet_secp_generator_entry
  C.jet_secp_generator_split_call C.jet_secp_generator_wnaf_setup
  C.jet_secp_generator_globals C.jet_secp_generator_point_stage C.jet_secp_generate_program
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate rescale_field_output.

Definition generator_main_stage := Ssequence generator_scalar_branch generator_point_stage.

Lemma generator_body_main_source : fn_body f_secp256k1_ecmult_strauss_wnaf=
  statement_sequence (firstn 8 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))))
    generator_main_stage.
Proof. reflexivity. Qed.

Lemma generator_denominator_one_bounds : square_input_bounds (point_set_bit_words Datatypes.true).
Proof.
  intros i Range;destruct i as [|[|[|[|[|i]]]]];try lia;
    cbn [point_set_bit_words Nat.eqb];rewrite ?Int64.unsigned_one,?Int64.unsigned_zero;lia.
Qed.
Lemma generator_denominator_one_value : radix_value (point_set_bit_words Datatypes.true) mod feP=1.
Proof. reflexivity. Qed.

Require Import C.jet_clight_forward C.jet_clight_internal_frame C.jet_secp_closed_helpers C.jet_clight_internal_preserve.

Theorem exec_generator_main_stage_forward le m value bp bng bt bz b0 b128 bw0 bw128 bj bn bl :
  let e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl in
  NoDup [bp;bt;bz;b0;b128;bw0;bw128;bj;bn;bl;bng] ->
  (forall h,generator_table_state h m) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_ng=Some (Vptr bng Ptrofs.zero) ->
  le!_no=Some (Vlong Int64.zero) -> le!_bits=Some (Vint Int.zero) ->
  scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
  fe_at m bz 0 (words5 (point_set_bit_words Datatypes.true)) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
  (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
    Mem.range_perm m b 0 hi Cur Freeable) ->
  (forall (high : bool) ma mi bs,Mem.alloc ma 0 32=(mi,bs) ->
    Mem.range_perm ma (if high then bw128 else bw0) 0 516 Cur Freeable -> exists mz,
    let b:=if high then bw128 else bw0 in let ba:=if high then b128 else b0 in
    Clight2.exec_stmt secp_ge (wnaf_env bs)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero)))
      mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  exists lef mf ox oy oz,
    Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
    lef!_r=Some (Vptr bp Ptrofs.zero) /\
    fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
    Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
    (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
      Mem.range_perm mf b 0 hi Cur Freeable) /\
    square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
    ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
      @literal_generate Alg.CoreFunSem value /\
    lframe (fun b _=>b<>bp /\ ~In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf /\ mem_forward m mf.
Proof.
  cbn zeta;intros Sep Tables PR NG No Bits Input Denominator PF SF Free ZeroSteps.
  set (e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) in *.
  pose proof Sep as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
  assert (S0S128:b0<>b128) by intuition congruence.
  assert (S0NG:b0<>bng) by intuition congruence.
  assert (S128NG:b128<>bng) by intuition congruence.
  assert (SplitSep:NoDup [b0;b128;bw0;bw128]).
  { repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
  assert (PointSep:NoDup [bp;bt;bz;bw0;bw128]).
  { repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
  assert (Present:Cop.bool_val (Vptr bng Ptrofs.zero) (tptr (Tstruct __5826 noattr)) m=Some Datatypes.true).
  { change ((if Mem.weak_valid_pointer m bng 0 then Some Datatypes.true else None)=Some Datatypes.true).
    assert (Pointer:Mem.weak_valid_pointer m bng 0=Datatypes.true).
    { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
      eapply Mem.perm_implies;[exact (SF 0 ltac:(clear;lia))|apply perm_any_N]. }
    rewrite Pointer;reflexivity. }
  assert (LocalSize:forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) -> 0<hi).
  { intros b hi Slot;clear -Slot;cbn [generator_local_storage In] in Slot.
    repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
      inversion Slot;lia. }
  destruct (exec_generator_scalar_split e le m value b0 b128 bng 0
    eq_refl eq_refl eq_refl NG S0S128 S0NG S128NG
    (Free b0 32 ltac:(cbn [generator_local_storage In];tauto))
    (Free b128 32 ltac:(cbn [generator_local_storage In];tauto)) Input)
    as (ms & Split & Low & High & FL & FH & BlocksS & PermS & FrameS).
  assert (FreeS:forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
    Mem.range_perm ms b 0 hi Cur Freeable).
  { intros b hi Slot pos Range;apply (proj2 (PermS b pos Cur Freeable));apply (Free b hi Slot);exact Range. }
  assert (TablesS:forall h,generator_table_state h ms).
  { intro h;destruct (Tables h) as [Table Readonly].
    assert (Outside:generator_table_block h<>b0 /\ generator_table_block h<>b128 /\ generator_table_block h<>bng).
    { repeat split;intro Same;rewrite Same in Readonly.
      - destruct (proj1 (Readonly 0 Cur Freeable)
          (Free b0 32 ltac:(cbn [generator_local_storage In];tauto) 0 ltac:(clear;lia))) as [_ Order];inversion Order.
      - destruct (proj1 (Readonly 0 Cur Freeable)
          (Free b128 32 ltac:(cbn [generator_local_storage In];tauto) 0 ltac:(clear;lia))) as [_ Order];inversion Order.
      - destruct (proj1 (Readonly 0 Cur Freeable) (SF 0 ltac:(clear;lia))) as [_ Order];inversion Order. }
    split.
    - eapply generator_table_rep_lframe;[exact Table|exact FrameS|intros;exact Outside].
    - intros pos k p;rewrite PermS;apply Readonly. }
  assert (DenominatorS:fe_at ms bz 0 (words5 (point_set_bit_words Datatypes.true))).
  { eapply field_at_lframe;[exact Denominator|exact FrameS|intros;intuition congruence]. }
  destruct (exec_generator_wnaf_setup e le ms (literal_split128_low value) (literal_split128_high value)
    b0 b128 bw0 bw128 SplitSep eq_refl eq_refl eq_refl eq_refl eq_refl Bits Low High
    (FreeS bw0 516 ltac:(cbn [generator_local_storage In];tauto))
    (FreeS bw128 516 ltac:(cbn [generator_local_storage In];tauto)) ZeroSteps)
    as (mw & last0 & last128 & digits0 & digits128 & Wnaf & Max & Count0 & Count128 & Temps &
        Array0 & Array128 & FW0 & FW128 & FrameW & Literal0 & Literal128 & PermW & TablesW).
  set (lw:=generator_wnaf_setup_temps le (last0+1) (last128+1)) in *.
  assert (DenominatorW:fe_at mw bz 0 (words5 (point_set_bit_words Datatypes.true))).
  { eapply field_at_lframe;[exact DenominatorS|exact FrameW|intros;intuition congruence]. }
  assert (FreeW:forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
    Mem.range_perm mw b 0 hi Cur Freeable).
  { intros b hi Slot pos Range;apply (proj2 (PermW b pos Cur Freeable
      ltac:(eapply Mem.perm_valid_block;apply (FreeS b hi Slot 0);
        pose proof (LocalSize b hi Slot) as Size;clear -Size;lia))).
    apply (FreeS b hi Slot);exact Range. }
  assert (PFW:Mem.range_perm mw bp 0 128 Cur Freeable).
  { intros pos Range;apply (proj2 (PermW bp pos Cur Freeable
      ltac:(eapply Mem.perm_valid_block;apply (proj2 (PermS bp 0 Cur Freeable));exact (PF 0 ltac:(clear;lia))))).
    apply (proj2 (PermS bp pos Cur Freeable));apply PF;exact Range. }
  assert (PRW:lw!_r=Some (Vptr bp Ptrofs.zero)) by (rewrite Temps by discriminate;exact PR).
  assert (NoW:lw!_no=Some (Vlong Int64.zero)) by (rewrite Temps by discriminate;exact No).
  destruct (exec_generator_point_stage e lw mw bp bt bz bw0 bw128 (point_set_bit_words Datatypes.true)
    (literal_split128_low value) (literal_split128_high value) digits0 digits128 last0 last128
    PointSep ltac:(intro h;apply TablesW,TablesS) PRW NoW Max Count0 Count128
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    Array0 Array128 Literal0 Literal128 generator_denominator_one_bounds generator_denominator_one_value
    DenominatorW PFW
    (FreeW bt 88 ltac:(cbn [generator_local_storage In];tauto))
    (FreeW bz 40 ltac:(cbn [generator_local_storage In];tauto)))
    as (lef & mf & ox & oy & oz & Point & PRF & X & Y & Z & Flag & DenominatorF & PFF & FTF & FZF &
        BX & BY & BZ & Literal & FrameP).
  assert (FreeF:forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
    Mem.range_perm mf b 0 hi Cur Freeable).
  { intros b hi Slot.
    destruct (peq b bt) as [->|NotT].
    - assert (Size:hi=88).
      { clear -Slot Distinct;cbn [generator_local_storage In] in Slot;
        repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
          inversion Slot;subst;intuition congruence. }
      subst hi;exact FTF.
    - destruct (peq b bz) as [->|NotZ].
      + assert (Size:hi=40).
        { clear -Slot Distinct;cbn [generator_local_storage In] in Slot;
          repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
            inversion Slot;subst;intuition congruence. }
        subst hi;exact FZF.
      + eapply curve_keep_free;[eapply LocalSize;exact Slot|exact (FreeW b hi Slot)|exact FrameP|].
        intros pos;split;[|split;assumption].
        clear -Slot Distinct;cbn [generator_local_storage In] in Slot;
          repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
            inversion Slot;subst;intuition congruence. }
  assert (SFF:Mem.range_perm mf bng 0 32 Cur Freeable).
  { eapply curve_keep_free with (P:=fun b _=>b<>bp /\ b<>bt /\ b<>bz);
      [clear;lia| |exact FrameP|intros;clear -Distinct;intuition congruence].
    intros pos Range;apply (proj2 (PermW bng pos Cur Freeable
      ltac:(eapply Mem.perm_valid_block;apply (proj2 (PermS bng 0 Cur Freeable));exact (SF 0 ltac:(clear;lia))))).
    apply (proj2 (PermS bng pos Cur Freeable));apply SF;exact Range. }
  assert (Frame:lframe (fun b _=>b<>bp /\ ~In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FrameS|].
      intros b pos [NotP [Outside NotNG]] Valid;clear -Outside NotNG;cbn [In] in Outside;intuition congruence.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact FrameW|].
        intros b pos [NotP [Outside NotNG]] Valid;clear -Outside;cbn [In] in Outside;intuition congruence.
      + eapply lframe_implies;[exact FrameP|].
        intros b pos [NotP [Outside NotNG]] Valid;clear -Outside NotP;cbn [In] in Outside;intuition congruence. }
  assert (ForwardS:mem_forward m ms).
  { intros block Valid;split.
    - exact (proj2 (proj2 FrameS) block Valid).
    - intros pos permission Perm;exact (proj1 (PermS block pos Memtype.Max permission) Perm). }
  assert (ForwardW:mem_forward ms mw).
  { intros block Valid;split.
    - exact (proj2 (proj2 FrameW) block Valid).
    - intros pos permission Perm;exact (proj1 (PermW block pos Memtype.Max permission Valid) Perm). }
  assert (ForwardPoint:mem_forward mw mf).
  { assert (Plain:plain_env e).
    { unfold e,generator_local_env;repeat (apply plain_set;[|reflexivity]);apply plain_empty. }
    assert (Closed:closed_stmtb secp_closed_helpers generator_point_stage=true) by (vm_compute;reflexivity).
    exact (proj1 (secp_closed_stmt_preserved e lw mw generator_point_stage E0 lef mf Out_normal Point Plain Closed)). }
  assert (Forward:mem_forward m mf) by
   (eapply mem_forward_trans;[exact ForwardS|eapply mem_forward_trans;[exact ForwardW|exact ForwardPoint]]).
  exists lef,mf,ox,oy,oz;split.
  - unfold generator_main_stage;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lw) (m1:=mw);[|exact Point].
    rewrite generator_scalar_branch_source;eapply exec_Sifthenelse
      with (v1:=Vptr bng Ptrofs.zero) (b:=Datatypes.true);[apply eval_Etempvar;exact NG|exact Present|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=ms);[exact Split|exact Wnaf].
  - split;[exact PRF|];split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact Flag|];
    split;[exact PFF|];split;[exact SFF|];split;[exact FreeF|];split;[exact BX|];split;[exact BY|];split;[exact BZ|];split.
    + exact (eq_trans Literal (eq_sym (literal_generate_value value))).
    + split;[exact Frame|exact Forward].
Qed.

Theorem exec_generator_main_stage le m value bp bng bt bz b0 b128 bw0 bw128 bj bn bl :
  let e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl in
  NoDup [bp;bt;bz;b0;b128;bw0;bw128;bj;bn;bl;bng] ->
  (forall h,generator_table_state h m) ->
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_ng=Some (Vptr bng Ptrofs.zero) ->
  le!_no=Some (Vlong Int64.zero) -> le!_bits=Some (Vint Int.zero) ->
  scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
  fe_at m bz 0 (words5 (point_set_bit_words Datatypes.true)) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
  (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
    Mem.range_perm m b 0 hi Cur Freeable) ->
  (forall (high : bool) ma mi bs,Mem.alloc ma 0 32=(mi,bs) ->
    Mem.range_perm ma (if high then bw128 else bw0) 0 516 Cur Freeable -> exists mz,
    let b:=if high then bw128 else bw0 in let ba:=if high then b128 else b0 in
    Clight2.exec_stmt secp_ge (wnaf_env bs)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero)))
      mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  exists lef mf ox oy oz,
    Clight2.exec_stmt secp_ge e le m generator_main_stage E0 lef mf Out_normal /\
    lef!_r=Some (Vptr bp Ptrofs.zero) /\
    fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
    Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
    (forall b hi,In (b,hi) (generator_local_storage bt bz b0 b128 bw0 bw128 bj bn bl) ->
      Mem.range_perm mf b 0 hi Cur Freeable) /\
    square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
    ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
      @literal_generate Alg.CoreFunSem value /\
    lframe (fun b _=>b<>bp /\ ~In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl] /\ b<>bng) m mf.
Proof.
 cbn zeta;intros Sep Tables PR NG No Bits Input Denominator PF SF Free ZeroSteps.
 destruct (exec_generator_main_stage_forward le m value bp bng bt bz b0 b128 bw0 bw128 bj bn bl
  Sep Tables PR NG No Bits Input Denominator PF SF Free ZeroSteps)
 as (lef & mf & ox & oy & oz & Run & PRF & X & Y & Z & Flag & PFF & SFF & FreeF & BX & BY & BZ & Literal & Frame & Forward).
 exists lef,mf,ox,oy,oz;repeat first [assumption|split].
Qed.
