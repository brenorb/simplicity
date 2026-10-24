(** Original ecmult on the public generate path: four actual allocations,
    all state stores, the checked Strauss call, and all four frees. The
    original external memset steps remain explicit deferred premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_columns C.jet_secp_rescale_literal C.jet_secp_canonical_scalar C.jet_secp_canonical_zero
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
  C.jet_secp_statement_prefix C.jet_secp_generator_zero_global C.jet_secp_generator_globals
  C.jet_secp_generator_startup C.jet_secp_generator_function C.jet_secp_generate_program
  C.jet_secp_ecmult_entry C.jet_secp_ecmult_state C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop
  C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate rescale_field_output canonical_scalar_normalize.

Lemma ecmult_local_blocks bx ba bps bs : blocks_of_env secp_ge (ecmult_env bx ba bps bs)=
  [(bs,0,24);(bx,0,320);(bps,0,1040);(ba,0,704)].
Proof. reflexivity. Qed.

Definition ecmult_strauss_call := snd (split_statement_last (fn_body f_secp256k1_ecmult)).
Lemma ecmult_body_source : fn_body f_secp256k1_ecmult=
  statement_sequence (fst (split_statement_last (fn_body f_secp256k1_ecmult))) ecmult_strauss_call.
Proof. reflexivity. Qed.
Lemma ecmult_strauss_call_source : ecmult_strauss_call=
  curve_call _secp256k1_ecmult_strauss_wnaf f_secp256k1_ecmult_strauss_wnaf None
    [Eaddrof (Evar _state (Tstruct _secp256k1_strauss_state noattr))
       (tptr (Tstruct _secp256k1_strauss_state noattr));
     Etempvar _r (tptr (Tstruct __6123 noattr));Econst_int Int.one tint;
     Etempvar _a (tptr (Tstruct __6123 noattr));Etempvar _na (tptr (Tstruct __5826 noattr));
     Etempvar _ng (tptr (Tstruct __5826 noattr))].
Proof. reflexivity. Qed.

Theorem eval_ecmult_generator value m bp bng ap :
  generator_startup m -> bp<>bng ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
  scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
  (forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero)))
      mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  exists mf ox oy oz,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
      [Vptr bp Ptrofs.zero;Vptr ap Ptrofs.zero;Vptr generator_zero_block Ptrofs.zero;Vptr bng Ptrofs.zero]
      E0 mf Vundef /\
    fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
    Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
    square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
    ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
      @literal_generate Alg.CoreFunSem value /\
    generator_startup mf /\ lframe (fun b _=>b<>bp /\ b<>bng) m mf.
Proof.
  intros Ready Separate PF SF Input ZeroSteps.
  assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;exact (PF 0 ltac:(clear;lia))).
  assert (VS:Mem.valid_block m bng) by (eapply Mem.perm_valid_block;exact (SF 0 ltac:(clear;lia))).
  destruct (ecmult_entry_and_state m (Vptr bp Ptrofs.zero) (Vptr ap Ptrofs.zero)
    (Vptr generator_zero_block Ptrofs.zero) (Vptr bng Ptrofs.zero))
    as (mi & ms & bx & ba & bps & bs & Entry & Setup & LoadX & LoadA & LoadPS &
        Distinct & Fresh & OwnedS & PrepUnchanged).
  set (e:=ecmult_env bx ba bps bs) in *.
  set (le:=ecmult_temps (Vptr bp Ptrofs.zero) (Vptr ap Ptrofs.zero)
    (Vptr generator_zero_block Ptrofs.zero) (Vptr bng Ptrofs.zero)) in *.
  assert (Old:forall b,Mem.valid_block m b -> b<>bx /\ b<>ba /\ b<>bps /\ b<>bs).
  { intros b Valid;pose proof (Fresh b Valid) as Outside.
    clear -Outside;cbn [In] in Outside;intuition congruence. }
  assert (PrepFrame:lframe (fun _ _=>True) m ms).
  { apply lframe_unchanged;exact PrepUnchanged. }
  assert (ReadyS:generator_startup ms).
  { eapply generator_startup_lframe;[exact Ready| |exact PrepFrame|intros;exact I|intros;exact I].
    eapply mem_forward_trans;[eapply clight_entry2_forward;exact Entry|].
    exact (proj1 (clight_exec_forward secp_ge) _ _ _ _ _ _ _ _ Setup). }
  assert (PFS:Mem.range_perm ms bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact PF|exact PrepFrame|intros;exact I]. }
  assert (SFS:Mem.range_perm ms bng 0 32 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact SF|exact PrepFrame|intros;exact I]. }
  assert (InputS:scalar_at ms bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value))))).
  { eapply scalar_at_lframe;[exact Input|exact PrepFrame|intros;exact I]. }
  destruct (eval_generator_strauss_from_owned value ms bs bx ba bp bng (Vptr ap Ptrofs.zero)
    (proj1 ReadyS) (proj2 ReadyS) LoadX LoadA Separate PFS SFS InputS ZeroSteps)
    as (mc & ox & oy & oz & Strauss & X & Y & Z & Flag & PFC & SFC & BX & BY & BZ & Literal & CFrame).
  assert (Call:Clight2.exec_stmt secp_ge e le ms ecmult_strauss_call E0 le mc Out_normal).
  { rewrite ecmult_strauss_call_source;eapply exec_curve_call with
      (vargs:=[Vptr bs Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.one;Vptr ap Ptrofs.zero;
        Vptr generator_zero_block Ptrofs.zero;Vptr bng Ptrofs.zero]) (v:=Vundef).
    - unfold secp_pure;repeat first [left;reflexivity|right].
    - reflexivity.
    - eapply eval_Econs with (v1:=Vptr bs Ptrofs.zero).
      + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      + reflexivity.
      + eapply eval_Econs with (v1:=Vptr bp Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|].
        eapply eval_Econs with (v1:=Vint Int.one);[constructor|reflexivity|].
        eapply eval_Econs with (v1:=Vptr ap Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|].
        eapply eval_Econs with (v1:=Vptr generator_zero_block Ptrofs.zero);
          [apply eval_Etempvar;reflexivity|reflexivity|].
        eapply eval_Econs with (v1:=Vptr bng Ptrofs.zero);[apply eval_Etempvar;reflexivity|reflexivity|constructor].
    - exact Strauss. }
  assert (OwnedC:forall b hi,In (b,hi) [(bx,320);(ba,704);(bps,1040);(bs,24)] ->
    Mem.range_perm mc b 0 hi Cur Freeable).
  { intros b hi Slot.
    assert (Size:0<hi) by (clear -Slot;destruct Slot as [E|[E|[E|[E|[]]]]];injection E;intros;subst;lia).
    eapply curve_keep_free;[exact Size|exact (OwnedS b hi Slot)|exact CFrame|].
    intros pos;destruct (Old bp VP) as (PX & PA & PPS & PS);
      destruct (Old bng VS) as (SX & SA & SPS & SS).
    clear -Slot PX PA PPS PS SX SA SPS SS.
    destruct Slot as [E|[E|[E|[E|[]]]]];injection E;intros;subst;split;congruence. }
  destruct (free_list_exists [(bs,0,24);(bx,0,320);(bps,0,1040);(ba,0,704)] mc)
    as (mf & Released & Unchanged).
  - pose proof Distinct as D;repeat rewrite NoDup_cons_iff in D;cbn [In] in D.
    clear -D;cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi Slot;clear -OwnedC Slot;destruct Slot as [E|[E|[E|[E|[]]]]];
      injection E;intros;subst;apply OwnedC;cbn [In];tauto.
  - assert (FFrame:lframe (fun b _=>b<>bx /\ b<>ba /\ b<>bps /\ b<>bs) mc mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
    assert (XF:fe_at mf bp 0 (words5 ox)).
    { eapply field_at_lframe;[exact X|exact FFrame|intros;apply Old;exact VP]. }
    assert (YF:fe_at mf bp 40 (words5 oy)).
    { eapply field_at_lframe;[exact Y|exact FFrame|intros;apply Old;exact VP]. }
    assert (ZF:fe_at mf bp 80 (words5 oz)).
    { eapply field_at_lframe;[exact Z|exact FFrame|intros;apply Old;exact VP]. }
    assert (FlagF:Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
    { rewrite (proj1 FFrame Mint32 bp 120);[exact Flag| |intros;apply Old;exact VP].
      eapply Mem.perm_valid_block;exact (PFC 0 ltac:(clear;lia)). }
    assert (PFF:Mem.range_perm mf bp 0 128 Cur Freeable).
    { eapply curve_keep_free;[clear;lia|exact PFC|exact FFrame|intros;apply Old;exact VP]. }
    assert (SFF:Mem.range_perm mf bng 0 32 Cur Freeable).
    { eapply curve_keep_free;[clear;lia|exact SFC|exact FFrame|intros;apply Old;exact VS]. }
    assert (Frame:lframe (fun b _=>b<>bp /\ b<>bng) m mf).
    { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>bng).
      - eapply lframe_trans.
        + eapply lframe_implies;[exact PrepFrame|intros;exact I].
        + eapply lframe_trans.
          * eapply lframe_implies;[exact CFrame|intros b pos [Valid Outside] _;exact Outside].
          * eapply lframe_implies;[exact FFrame|intros b pos [Valid Outside] _;apply Old;exact Valid].
      - intros b pos Outside Valid;split;assumption. }
    assert (Whole:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult)
      [Vptr bp Ptrofs.zero;Vptr ap Ptrofs.zero;Vptr generator_zero_block Ptrofs.zero;Vptr bng Ptrofs.zero]
      E0 mf Vundef).
    { eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=le) (m1:=mi) (m2:=mc) (out:=Out_normal).
      - exact Entry.
      - rewrite ecmult_body_source;eapply exec_statement_prefix_then_last;[exact Setup|exact Call].
      - reflexivity.
      - unfold e;rewrite ecmult_local_blocks;exact Released. }
    assert (ReadyF:generator_startup mf).
    { destruct (generator_startup_separate m bp 128 Ready ltac:(clear;lia) PF) as [PZ PT].
      destruct (generator_startup_separate m bng 32 Ready ltac:(clear;lia) SF) as [SZ ST].
      eapply generator_startup_call;[exact Ready|exact Whole|exact Frame| |].
      - intros pos;clear -PZ SZ;split;congruence.
      - intros h pos;specialize (PT h);specialize (ST h);clear -PT ST;split;congruence. }
    exists mf,ox,oy,oz;split;[exact Whole|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];
      split;[exact FlagF|];split;[exact PFF|];split;[exact SFF|];split;[exact BX|];split;[exact BY|];
      split;[exact BZ|];split;[exact Literal|];split;[exact ReadyF|exact Frame].
Qed.
